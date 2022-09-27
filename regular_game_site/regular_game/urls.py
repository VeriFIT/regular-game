from django.urls import path

from . import views

app_name = 'regular_game'
urlpatterns = [
    path('', views.IndexView.as_view(), name='index'),
    path('player/<int:player_id>/', views.task, name='task'),
    path('start/', views.start_game, name='start_game'),
    path('player/<int:player_id>/answer', views.answer, name='answer'),
    path('player/<int:player_id>/endgame', views.endgame, name='endgame'),
]
