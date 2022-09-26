from django.urls import path

from . import views

app_name = 'regular_game'
urlpatterns = [
    path('', views.IndexView.as_view(), name='index'),
]
