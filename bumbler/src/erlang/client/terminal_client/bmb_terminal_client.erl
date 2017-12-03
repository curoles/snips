%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Erlang Node Terminal Client Application.
%%
-module(bmb_terminal_client).


-export([start/0]).

start() ->
    io:format("Loading Erlang Node Terminal Client Application.~n"),
    application:load(bmb_terminal_client_app),
    io:format("Starting Erlang Node Terminal Client Application.~n"),
    application:start(bmb_terminal_client_app).
