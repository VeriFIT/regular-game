from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import generic

from datetime import datetime, timedelta
import re

from .models import *

def get_tasks_cnt():
    return Task.objects.all().order_by('-num')[0].num

# penalty for skipping a task
SKIP_PENALTY = 30

# Main page with high score chart
class IndexView(generic.ListView):
    template_name = 'regular_game/index.html'
    context_object_name = 'highscore_list'

    def get_queryset(self):
        """Return at most 10 players with the highest scores."""
        return Player.objects.filter(finished=True).order_by('score')[:10]

# a method for starting the game
def start_game(request):
    if 'plname' not in request.POST or not request.POST['plname']:
        return render(request, 'regular_game/index.html', {
            'error_message': "Zadejte jméno hráče.",
            'highscore_list': IndexView().get_queryset()
        })

    plname = request.POST['plname']

    player = Player()
    player.name = plname
    # Quick timezone hack
    player.time_begin = datetime.now() + timedelta(hours=2)
    player.score = 0
    player.next_task = 1
    player.save()

    return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))


# common rendering of the task page
def render_next_task_with(request, player, regex=None, error_msg=None, bad_pos=None, bad_neg=None):
    task = get_object_or_404(Task, num=player.next_task)
    snippets = task.snippet_set.all()
    pos_snips = [snip for snip in snippets if snip.snip_type == 'Y']
    neg_snips = [snip for snip in snippets if snip.snip_type == 'N']
    return render(request, 'regular_game/task.html',
                  {
                      'player': player,
                      'task': task,
                      'regex': regex,
                      'regex_len': len(regex) if regex else 0,
                      'pos_snips': pos_snips,
                      'neg_snips': neg_snips,
                      'tasks_cnt': get_tasks_cnt(),
                      'tasks_done': task.num - 1,
                      'progress': 100 / get_tasks_cnt() * (task.num - 1),
                      'error_message': error_msg,
                      'bad_pos': bad_pos,
                      'bad_neg': bad_neg,
                      'best_sol_len': len(task.best_solution) if task.best_solution else None,
                      'best_sol_player': task.best_solution_player
                  })


# A page with one step of the game
def task(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    if player.next_task == get_tasks_cnt() + 1:
        player.finished = True
        # Quick timezone hack
        player.time_end = datetime.now() + timedelta(hours=2)
        player.save()
        return HttpResponseRedirect(reverse('regular_game:endgame', args=(player.pk,)))
    else:
        return render_next_task_with(request, player)


# a method for answering a task
def answer(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    if 'skip' in request.POST:
        player.score += SKIP_PENALTY
        player.next_task += 1
        player.save()
        return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))
    elif 'giveup' in request.POST:
        player.score += (get_tasks_cnt() - player.next_task + 1) * SKIP_PENALTY
        player.next_task = get_tasks_cnt() + 1
        player.save()
        return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))

    task = get_object_or_404(Task, num=player.next_task)
    snippets = task.snippet_set.all()
    pos_snips = [snip for snip in snippets if snip.snip_type == 'Y']
    neg_snips = [snip for snip in snippets if snip.snip_type == 'N']

    if 'regex' not in request.POST or not request.POST['regex']:
        return render_next_task_with(request, player, error_msg="Zadejte regex!")

    regex = request.POST['regex']
    correct = True
    bad_pos = []
    bad_neg = []
    try:
        for snip in pos_snips:   # we need to match all examples
            if not re.search(regex, snip.text):
                correct = correct and False
                bad_pos += [snip]

        for snip in neg_snips:   # we need to reject all counterexamples
            if re.search(regex, snip.text):
                correct = correct and False
                bad_neg += [snip]

    except Exception as error:
        return render_next_task_with(request, player, regex=regex, error_msg=f"Špatně zadaný regex! (popis chyby: \"{error}\")")

    if not correct:
        return render_next_task_with(request, player, regex, error_msg=f"Špatný regex \"{regex}\"!", bad_pos=bad_pos, bad_neg=bad_neg)

    player.next_task += 1
    player.score += len(regex)

    if not task.best_solution or len(regex) < len(task.best_solution):
        task.best_solution = regex
        task.best_solution_player = player
        task.save()

    player.save()

    return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))

# end of game
def endgame(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    return render(request, 'regular_game/index.html',
                    {
                        'player': player,
                        'highscore_list': IndexView().get_queryset()
                    })
