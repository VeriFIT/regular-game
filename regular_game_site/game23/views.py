from django.shortcuts import render
from django.views import generic


# Main page with high score chart
class IndexView(generic.ListView):
    template_name = 'game23/index.html'
    context_object_name = 'highscore_list'

    def get_queryset(self):
        """Return at most 10 players with the highest scores."""
        # highscore = Player.objects.filter(finished=True).order_by('score')[:10]
        # highscore = sorted(highscore, key = lambda x: (x.score, x.duration))
        highscore = []
        return highscore
