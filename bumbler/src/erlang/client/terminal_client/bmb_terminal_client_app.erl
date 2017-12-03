%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Bumbler Terminal Messenger client application.
%% Implemented as Erlang node.
%%
-module(bmb_terminal_client_app).
-behaviour(application).

-export([start/2, stop/1, loop/1, send/2, connect/2]).

client_id() ->
    atom_to_list(node()).

start(_Type, _Args) ->
    io:format("Starting.~n"),
    ThisClientPID = spawn(bmb_terminal_client_app, loop, [client_id()]),
    io:format("This client PID=~p.~n", [ThisClientPID]),
    register(this, ThisClientPID),
    %Hostname = net_adm:localhost(),
    %ServerNodeName = "bumbler@" ++ Hostname,
    %io:format("Ping server:~p.~n", [ServerNodeName]),
    %Pong = net_adm:ping(list_to_atom(ServerNodeName)),
    %io:format("Pong:~p.~n", [Pong]),
    connect(client_id(), ThisClientPID),
    {ok, self()}.

stop(_State) ->
    ok.

%% @doc Message receiving loop.
%%
%%
loop(ThisClientId) ->

    % Receive message.
    receive
        % Message from itself.
        {client, ThisClientId, ThisClientId, MsgString} ->
            io:format("Message from itself:~s.~n",[MsgString]),
            loop(ThisClientId);

        % Message from another client.
        {client, SenderId, ThisClientId, MsgString} ->
            io:format("Message from ~s:~s.~n",[SenderId, MsgString]),
            loop(ThisClientId);

        % Message to someone else.
        {client, SenderId, RecipientId, MsgString} ->
            io:format("Oops. Message from ~s to ~s:~s.~n",[SenderId, RecipientId, MsgString]),
            loop(ThisClientId);

        {send_bmb_msg, RecipientId, MsgString} ->
            io:format("Send to ~p: ~p.~n", [RecipientId, MsgString]),
            {msg_gate_process, server_name()} ! {client, ThisClientId, RecipientId, MsgString},
            loop(ThisClientId);

        % Unknown message.
        _ ->
            io:format("Oops. Unknown message.~n"),
            loop(ThisClientId)

    end.

%% @doc Returns Bumbler server Erlang node name as string.
%%
server_name_string() ->
    "bumbler@" ++ net_adm:localhost().

%% @doc Returns Bumbler server Erlang node nameas atom.
%%
server_name() ->
    list_to_atom(server_name_string()).

%% @doc Returns true if Bumbler server node is running
%% and returning ping.
%%
is_server_running() ->
    %io:format("Ping server:~p.~n", [ServerNodeName]),
    Pong = net_adm:ping(server_name()),
    Pong == pong. % reply is pong|pang

connect(ThisClientId, ThisClientPID) -> 
    net_kernel:connect_node(server_name()),
    case is_server_running() of
       true  -> {msg_gate_process, server_name()} !
                {register_client, ThisClientId, ThisClientPID};
       false -> error
    end.

%% @doc Sends message to Bumbler server.
%%
send(RecipientId, MsgString) ->
    case is_server_running() of
       true  -> this ! {send_bmb_msg, RecipientId, MsgString};
       false -> error
    end.


