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
        return f"{self.name} (task: {self.next_task}, score: {self.score})"

    @property
    def duration(self):
        return self.time_end - self.time_begin

    @property
    def time_begin_str(self):
        return self.time_begin.strftime("%d.%m.%Y %H:%M:%S")

    @property
    def duration_str(self):
        dur = self.time_end - self.time_begin
        hours, minutes = dur.seconds // 3600, dur.seconds %3600//60
        seconds = dur.seconds - hours*3600 - minutes*60 + dur.microseconds / 1e6
        return f"{hours}h {minutes}m {seconds:.2f}s"

# A task - one step of the game
class Task(models.Model):
    title = models.CharField(max_length=200)
    num = models.IntegerField()
    text = models.TextField()
    best_solution = models.TextField(null=True)
    best_solution_player = models.ForeignKey(Player, null=True, on_delete=models.SET_NULL)

    def __str__(self):
        if self.best_solution_player:
            best_player_name = self.best_solution_player.name
            best_sol_len = len(self.best_solution)
        else:
            best_player_name = ""
            best_sol_len = 0

        return f"{self.num}: {self.title} (record - {best_player_name}: {best_sol_len})"


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
