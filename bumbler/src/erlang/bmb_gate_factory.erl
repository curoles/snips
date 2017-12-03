%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Gate Factory creates Message Gate and monitors its health.
%% It restarts the (Gate) process whenever the process dies.
%%
%% Use:
%% ```
%% GateFactory = spawn(fun bmb_gate_factory:loop/0).
%% GateFactory ! new
%% '''
%%
%% To simulate exit programmatically:
%% ```
%% exit({module_name,die,at,erlang:time()})
%% '''
%%
-module(bmb_gate_factory).
-author('Igor Lesik').

-export([loop/0]).

instance_name() ->
    bmb_util:module_instance_name("GateFactory").

%% @doc Message receiving loop.
%%
%%
loop() ->
    % Register the process as one that will trap exits.
    process_flag(trap_exit, true),

    % Receive message.
    receive
        % Request to create new Message Gate.
        new ->
            io:format("~s Creating new Gate process.~n", [instance_name()]),
            % Spawn new process and map atom to PID.
            register(msg_gate_process, spawn_link(bmb_msg_gate, loop, [#{},#{}])),
            loop();

        % Handle the exit message.
        {'EXIT', From, Reason} ->
            io:format("~s Gate ~p died with reason ~p.~n",
                [instance_name(), From, Reason]),
            io:format("~s Restarting Gate.~n", [instance_name()]),
            % Send message 'new' to itself to re-create the process.
            self() ! new,
            loop()
    end.
