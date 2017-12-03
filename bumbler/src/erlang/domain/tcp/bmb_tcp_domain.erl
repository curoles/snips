%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Domain of TCP clients.
%%
%% @see http://erlang.org/doc/man/gen_tcp.html
%%
%%
-module(bmb_tcp_domain).
-author('Igor Lesik').

-include("mqtt_defines.hrl").

-export([start/2, loop/3, accept_connection/1]).

instance_name() ->
    bmb_util:module_instance_name("TCP").

start(Id, UpLinkPID) ->
    PID = spawn(?MODULE, loop, [Id, UpLinkPID, #{}]),
    io:format("~s started as ~s.~n", [instance_name(), Id]),
    {ok, ListenSocket} = gen_tcp:listen(?MQTT_TCP_PORT,
        [{active,false}, binary, {packet, 1}]),
        %[{active,true}, binary]),
    spawn(?MODULE, accept_connection, [ListenSocket]),
    PID.

accept_connection(ListenSocket) ->
    %{ok, AcceptSocket} = gen_tcp:accept(ListenSocket).
    {ok, AcceptSocket} = gen_tcp:accept(ListenSocket),
    io:format("~s connection accepted socket=~p.~n",
        [instance_name(), AcceptSocket]),
    {ok, BinData} = recv_on_socket(AcceptSocket, []),
    io:format("~s rcvd:~p~n", [instance_name(), BinData]),
    ok = gen_tcp:close(AcceptSocket),
    ok.

recv_on_socket(Sock, Bs) ->
    case gen_tcp:recv(Sock, 0) of
        {ok, B} ->
            io:format("rcv so far:~p~n", [[Bs, B]]),
            recv_on_socket(Sock, [Bs, B]);
        {error, closed} ->
            {ok, list_to_binary(Bs)}
    end.

%% @doc Message receiving loop.
%%
%%
loop(ThisClientId, UpLinkPID, ClientMap) ->

    % Receive message.
    receive
%        % Message to register a child client.
%        {register_client, ClientId, ClientPID} ->
%            io:format("~s Register client:~p, PID=~p.~n",
%                [instance_name(), ClientId, ClientPID]),
%            NewClientMap = ClientMap#{ClientId => ClientPID},
%            loop(ThisClientId, UpLinkPID, NewClientMap);
%
%        % Forward message.
%        {forward, SenderId, RecipientId, MsgString} ->
%            io:format("~s forward from ~s to ~s:~p.~n",
%                [instance_name(), SenderId, RecipientId, MsgString]),
%            forward(SenderId, RecipientId, MsgString, ClientMap),
%            loop(ThisClientId, UpLinkPID, ClientMap);
%
%        % Send message UP.
%        {client, SenderId, RecipientId, MsgString} ->
%            io:format("~s from ~s to ~s:~p.~n",
%                [instance_name(), SenderId, RecipientId, MsgString]),
%            % TODO check if receipient is inside the domain
%            UpLinkPID ! {client, ThisClientId++":"++SenderId, RecipientId, MsgString},
%            loop(ThisClientId, UpLinkPID, ClientMap);

        % Unknown message.
        Msg ->
            io:format("~s Unknown message ~p.~n", [instance_name(), Msg]),
            loop(ThisClientId, UpLinkPID, ClientMap)

    end.

