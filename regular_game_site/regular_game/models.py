from django.db import models


# A player for a game
class Player(models.Model):
    name = models.CharField(max_length=200)
    time_begin = models.DateTimeField('time of game start')
    time_end =  models.DateTimeField('time of game end', null=True)
    score = models.IntegerField()
    next_task = models.IntegerField()   # next task for the player to take

    def __str__(self):
        return f"{self.name} ({self.score})"


# A task - one step of the game
class Task(models.Model):
    title = models.CharField(max_length=200)
    num = models.IntegerField()
    text = models.TextField()

    def __str__(self):
        return f"{self.num}: {self.title}"
