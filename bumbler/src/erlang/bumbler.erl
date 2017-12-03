%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Starts all applications.
%%
-module(bumbler).

-export([start/0]).

instance_name() ->
    bmb_util:module_instance_name("Bumbler").

%start() ->
%    application:start(inets). %,
%%    application:start(XYZ).

start() ->
    io:format("~s Loading Bumbler App.~n", [instance_name()]),
    application:load(bumbler_app),
    application:start(bumbler_app).
