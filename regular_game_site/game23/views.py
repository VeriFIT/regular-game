from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import generic

from datetime import datetime, timedelta

# import z3

from .models import *
from .solver import cond_satisfied


def get_tasks_cnt():
    task_with_highest_num = Task.objects.all().order_by('-num').first()
    if task_with_highest_num:
        return task_with_highest_num.num
    return 0


# Main page with high score chart
class IndexView(generic.ListView):
    template_name = 'game23/index.html'
    context_object_name = 'highscore_list'

    def get_queryset(self):
        """Return at most 10 players with the highest scores."""
        highscore = Player.objects.filter(finished=True).order_by('-score')[:10]
        # We need to sort by descending duration and ascending score
        highscore = sorted(
            sorted(highscore, key = lambda x: x.duration),
            key=lambda x: x.score,
            reverse=True
        )
        return highscore


# a method for starting the game
def start_game(request):
    if 'plname' not in request.POST or not request.POST['plname']:
        return render(request, 'game23/index.html', {
            'error_message': "Zadejte jméno hráče.",
            'highscore_list': IndexView().get_queryset()
        })

    plname = request.POST['plname']
    avatar = request.POST['avatar']

    player = Player()
    player.name = plname
    player.difficulty = Difficulty.objects.get(avatar=avatar)
    # Quick timezone hack
    player.time_begin = datetime.now() + timedelta(hours=2)
    player.score = 0
    player.next_task = 1
    player.save()

    return HttpResponseRedirect(reverse('game23:task', args=(player.pk,)))


# common rendering of the task page
def render_next_task_with(request, player, result=None, error_msg=None, cond=None):
    task = get_object_or_404(Task, num=player.next_task)
    diff_conds = {t: None for t in task.condition_set.filter(difficulty=player.difficulty)}
    return render(request, 'game23/task.html',
                  {
                      'player': player,
                      'task': task,
                      'result': result,
                      'result_len': len(result) if result else 0,
                      'conditions': cond if cond is not None else diff_conds,
                      'tasks_cnt': get_tasks_cnt(),
                      'tasks_done': task.num - 1,
                      'progress': 100 / get_tasks_cnt() * (task.num - 1),
                      'error_message': error_msg,
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
        return HttpResponseRedirect(reverse('game23:endgame', args=(player.pk,)))
    else:
        return render_next_task_with(request, player)


# a method for answering a task
def answer(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    if 'skip' in request.POST:
        player.score += player.difficulty.task_skip_score
        player.next_task += 1
        player.save()
        return HttpResponseRedirect(reverse('game23:task', args=(player.pk,)))
    elif 'giveup' in request.POST:
        player.score += (get_tasks_cnt() - player.next_task + 1) * player.difficulty.task_skip_score
        player.next_task = get_tasks_cnt() + 1
        player.save()
        return HttpResponseRedirect(reverse('game23:task', args=(player.pk,)))

    task = get_object_or_404(Task, num=player.next_task)

    if 'result' not in request.POST or not request.POST['result']:
        return render_next_task_with(request, player, error_msg="Zadejte odpověď!")

    result = request.POST['result']
    correct = True

    conditions = {t: None for t in task.condition_set.filter(difficulty=player.difficulty)}

    try:
        for cond in conditions.keys():   # we need to match all examples
            if not cond_satisfied(cond, result):
                correct = correct and False
                conditions[cond] = False
            else:
                conditions[cond] = True
    except Exception as error:
        return render_next_task_with(
            request,
            player,
            result=result,
            error_msg=f"Špatně zadaná odpověď či jiná chyba! (popis chyby: \"{error}\")",
            cond=conditions
        )

    if not correct:
        player.score += player.difficulty.task_fail_score
        player.save()
        return render_next_task_with(
            request, player, result, error_msg=f"Špatná odpověď \"{result}\"!", cond=conditions
        )

    player.next_task += 1
    player.score += player.difficulty.task_ok_score

    if not task.best_solution or len(result) < len(task.best_solution):
        task.best_solution = result
        task.best_solution_player = player
        task.save()

    player.save()

    return HttpResponseRedirect(reverse('game23:task', args=(player.pk,)))


# end of game
def endgame(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    return render(request, 'game23/index.html',
                    {
                        'player': player,
                        'highscore_list': IndexView().get_queryset()
                    })

# final solution
def solution(request):
    return render(request, 'game23/solution.html', {})

# solution submit
def solution_subm(request):
    correct_num = 0
    wrong_ans = []
    post_names = []
    post_names_list = ["", "logických hádanek", "hledání chyb v kódu", "vizuálního programování", "webové hry"]
    for i in range(1,5):
        box_id = f"answer{i}"
        if box_id not in request.POST or not request.POST[box_id]:
            continue
        else:
            answer = request.POST[box_id]

            try:
                # print(f"stand = {i}, value = {answer}")
                PartialKey.objects.get(stand=i, value=answer)
                correct_num += 1
                post_names += [post_names_list[i]]
            except:
                wrong_ans.append(answer)


    if wrong_ans:
        return render(request, 'game23/solution.html', {'wrong_answers': wrong_ans})
    else:
        return render(request, 'game23/solution.html', {'points': correct_num, 'trophies': post_names})
