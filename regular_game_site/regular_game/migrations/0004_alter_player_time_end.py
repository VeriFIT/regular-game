# Generated by Django 4.1.1 on 2022-09-26 20:06

from django.db import migrations, models


class Migration(migrations.Migration):

    dependencies = [
        ('regular_game', '0003_task_num'),
    ]

    operations = [
        migrations.AlterField(
            model_name='player',
            name='time_end',
            field=models.DateTimeField(null=True, verbose_name='time of game end'),
        ),
    ]
