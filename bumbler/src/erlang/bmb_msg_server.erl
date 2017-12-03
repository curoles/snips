%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc Bumbler Message Server.
%%
-module(bmb_msg_server).
-author('Igor Lesik').

-export([loop/0]).

%% @doc Loops receiving messages.
%%
loop() ->
    receive
        {client, SenderId, RecipientId, MsgString} ->
            io:format("server from ~p to ~p: ~s~n",
                [SenderId, RecipientId, MsgString]),
            forward_message(SenderId, RecipientId, MsgString),
            loop();
        _ ->
            io:format("server received some junk~n"),
            loop()
    end.

%% @doc Sends message to Recipient.
%%
forward_message(SenderId, RecipientId, MsgString) ->
    % for now let us just send back to the gate
    msg_gate_process ! {server, SenderId, RecipientId, MsgString},
    ok.
