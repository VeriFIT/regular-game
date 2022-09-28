from django.db import models


# A player for a game
class Player(models.Model):
    name = models.CharField(max_length=200)
    time_begin = models.DateTimeField('time of game start')
    time_end =  models.DateTimeField('time of game end', null=True)
    score = models.IntegerField()
    next_task = models.IntegerField()   # next task for the player to take
    finished = models.BooleanField(default=False)

    def __str__(self):
        return f"{self.name} ({self.score})"

    @property
    def duration(self):
        return self.time_end - self.time_begin


# A task - one step of the game
class Task(models.Model):
    title = models.CharField(max_length=200)
    num = models.IntegerField()
    text = models.TextField()
    best_solution = models.TextField(null=True)
    best_solution_player = models.ForeignKey(Player, null=True, on_delete=models.SET_NULL)

    def __str__(self):
        return f"{self.num}: {self.title}"


# a snippet of text used as a (counter)example for a task
class Snippet(models.Model):
    task = models.ForeignKey(Task, on_delete=models.CASCADE)
    text = models.TextField()
    snip_type = models.CharField(
                    max_length=1,
                    choices=[('Y', 'Yes'),
                             ('N', 'No')],
                    default='Y',
                )

    def __str__(self):
        return f'({self.snip_type}) {self.text}'
