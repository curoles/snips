-module(bmb_echo_client).
-author('Igor Lesik 2016').

-export([start/2, loop/2]).

instance_name() ->
    bmb_util:module_instance_name("Echo").

start(Id, ParentPID) ->
    io:format("~s starting as ~s.~n", [instance_name(), Id]),
    PID = spawn(bmb_echo_client, loop, [Id, ParentPID]),
    ParentPID ! {register_client, Id, PID},
    PID.

%% @doc Message receiving loop.
%%
%%
loop(ThisClientId, ParentPID) ->

    % Receive message.
    receive
        % Message from itself.
        {client, ThisClientId, ThisClientId, MsgString} ->
            io:format("~s Message from itself:~s.~n",
                [instance_name(), MsgString]),
            loop(ThisClientId, ParentPID);

        % Message from another client.
        {client, SenderId, ThisClientId, MsgString} ->
            io:format("~s Message from ~s:~s.~n",
                [instance_name(), SenderId, MsgString]),
            ParentPID ! {client, ThisClientId, SenderId, "Echo: "++MsgString},
            loop(ThisClientId, ParentPID);

        % Message to someone else.
        {client, SenderId, RecipientId, MsgString} ->
            io:format("~s Oops. Message from ~s to ~s:~s.~n",
                [instance_name(), SenderId, RecipientId, MsgString]),
            loop(ThisClientId, ParentPID)

    end.



