# Generated by Django 4.2.5 on 2023-09-19 20:20

from django.db import migrations, models


class Migration(migrations.Migration):

    initial = True

    dependencies = [
    ]

    operations = [
        migrations.CreateModel(
            name='Player',
            fields=[
                ('id', models.BigAutoField(auto_created=True, primary_key=True, serialize=False, verbose_name='ID')),
                ('name', models.CharField(max_length=200)),
                ('time_begin', models.DateTimeField(verbose_name='time of game start')),
                ('time_end', models.DateTimeField(null=True, verbose_name='time of game end')),
                ('score', models.IntegerField()),
                ('next_task', models.IntegerField()),
                ('finished', models.BooleanField(default=False)),
            ],
        ),
    ]
