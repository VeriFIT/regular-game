from django.http import HttpResponseRedirect
from django.shortcuts import get_object_or_404, render
from django.urls import reverse
from django.views import generic

from datetime import datetime

from .models import *

# Main page with high score chart
class IndexView(generic.ListView):
    template_name = 'regular_game/index.html'
    context_object_name = 'highscore_list'

    def get_queryset(self):
        """Return at most 10 players with the highest scores."""
        return Player.objects.order_by('-score')[:10]


# A page with one step of the game
def task(request, player_id):
    player = get_object_or_404(Player, pk=player_id)
    task_id = player.next_task
    task = get_object_or_404(Task, pk=task_id)
    return render(request, 'regular_game/task.html', {'player': player, 'task': task})


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

    player.next_task += 1
    player.save()

    return HttpResponseRedirect(reverse('regular_game:task', args=(player.pk,)))
