-module(bmb_msg_gate).
-author('Igor Lesik').

-export([loop/2]).

instance_name() ->
    bmb_util:module_instance_name("Gate").

%% @doc Message receiving loop.
%%
%% Topology:
%% client-A -> Gate -> Server -> Gate -> client-B
%%
loop(ClientList, DomainList) ->

    % Receive message.
    receive
        % Message from Client.
        {client, SenderId, RecipientId, MsgString} ->
            io:format("~s message from ~p to ~p:~s.~n",
                [instance_name(), SenderId, RecipientId, MsgString]),
            send_to_server(SenderId, RecipientId, MsgString),
            loop(ClientList, DomainList);

        % Message from Server.
        {server, SenderId, RecipientId, MsgString} ->
            receive_from_server(SenderId, RecipientId, MsgString, ClientList, DomainList),
            loop(ClientList, DomainList);

        % Register client.
        {register_client, ClientId, ClientPID} ->
            io:format("~s request to register client ~p, PID=~p.~n",
                [instance_name(), ClientId, ClientPID]),
            NewClientList = ClientList#{ClientId => ClientPID},
            loop(NewClientList, DomainList);

        % @TODO unregister client

        % Register domain.
        {register_domain, DomainId, DomainPID} ->
            io:format("~s request to register domain ~p, PID=~p.~n",
                [instance_name(), DomainId, DomainPID]),
            NewDomainList = DomainList#{DomainId => DomainPID},
            loop(ClientList, NewDomainList);

        % Unknown/unexpected message.
        UnknownMsg ->
            io:format("~s Unknown message: ~p.~n",[instance_name(), UnknownMsg]),
            loop(ClientList, DomainList)
    end.

send_to_server(SenderId, RecipientId, MsgString) ->
    io:format("~s gate->server from ~p to ~p msg: ~s~n",
        [instance_name(), SenderId, RecipientId, MsgString]),
    server_process ! {client, SenderId, RecipientId, MsgString},
    ok.

receive_from_server(SenderId, RecipientId, MsgString, ClientMap, DomainMap) ->
    io:format("~s server->gate from ~p to ~p msg: ~s~n",
        [instance_name(), SenderId, RecipientId, MsgString]),
    Domain = string:tokens(RecipientId, ":"),
    case Domain of
        [_|[]] -> forward(client, SenderId, RecipientId, MsgString, ClientMap);
        [H|T] -> forward(domain, H, SenderId, string:join(T,":"), MsgString, DomainMap)
    end.

forward(client, SenderId, RecipientId, MsgString, ClientMap) ->
    io:format("~s forward to client from ~p to ~p msg: ~s~n",
        [instance_name(), SenderId, RecipientId, MsgString]),
    case maps:find(RecipientId, ClientMap) of
        {ok, RecipientPID} -> RecipientPID ! {client, SenderId, RecipientId, MsgString};
        error -> error
    end.
forward(domain, Domain, SenderId, RecipientId, MsgString, DomainMap) ->
    io:format("~s forward to domain ~s from ~p to ~p msg: ~s~n",
        [instance_name(), Domain, SenderId, RecipientId, MsgString]),
    case maps:find(Domain, DomainMap) of
        {ok, DomainPID} -> DomainPID ! {forward, SenderId, RecipientId, MsgString};
        error -> error
    end.

