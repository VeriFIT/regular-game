from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import generic

from datetime import datetime
import re

from .models import *

# Main page with high score chart
class IndexView(generic.ListView):
    template_name = 'regular_game/index.html'
    context_object_name = 'highscore_list'

    def get_queryset(self):
        """Return at most 10 players with the highest scores."""
        return Player.objects.filter(finished=True).order_by('-score')[:10]


# A page with one step of the game
def task(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    task = get_object_or_404(Task, num=player.next_task)
    snippets = task.snippet_set.all()
    pos_snips = [snip for snip in snippets if snip.snip_type == 'Y']
    neg_snips = [snip for snip in snippets if snip.snip_type == 'N']
    return render(request, 'regular_game/task.html',
                  {
                      'player': player,
                      'task': task,
                      'pos_snips': pos_snips,
                      'neg_snips': neg_snips
                  })


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
    player.time_begin = datetime.now()
    player.score = 0
    player.next_task = 1
    player.save()

    return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))


# a method for answering a task
def answer(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    task = get_object_or_404(Task, num=player.next_task)
    snippets = task.snippet_set.all()
    pos_snips = [snip for snip in snippets if snip.snip_type == 'Y']
    neg_snips = [snip for snip in snippets if snip.snip_type == 'N']

    if 'regex' not in request.POST or not request.POST['regex']:
        return render(request, 'regular_game/task.html',
                        {
                            'player': player,
                            'task': task,
                            'pos_snips': pos_snips,
                            'neg_snips': neg_snips,
                            'error_message': "Zadejte regex!"
                        })

    regex = request.POST['regex']
    correct = True
    for snip in pos_snips:   # we need to match all examples
        if not re.search(regex, snip.text):
            correct = False
            break

    if correct:
        for snip in neg_snips:   # we need to reject all counterexamples
            if re.search(regex, snip.text):
                correct = False
                break

    if not correct:
        return render(request, 'regular_game/task.html',
                        {
                            'player': player,
                            'task': task,
                            'pos_snips': pos_snips,
                            'neg_snips': neg_snips,
                            'error_message': "Špatný regex!"
                        })


    player.next_task += 1
    player.score += 1
    player.save()

    if player.next_task == 3:   # end game
        player.finished = True
        player.time_end = datetime.now()
        player.save()
        return HttpResponseRedirect(reverse('regular_game:endgame', args=(player.pk,)))
    else:
        return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))

# end of game
def endgame(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    return render(request, 'regular_game/index.html',
                    {
                        'player': player,
                        'highscore_list': IndexView().get_queryset()
                    })
