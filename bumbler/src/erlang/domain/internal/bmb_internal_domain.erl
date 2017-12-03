%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Domain of internal services.
%%
-module(bmb_internal_domain).
-author('Igor Lesik').

-export([start/2, loop/3]).

instance_name() ->
    bmb_util:module_instance_name("InternalDm").

start(Id, UpLinkPID) ->
    PID = spawn(bmb_internal_domain, loop, [Id, UpLinkPID, #{}]),
    io:format("~s started as ~s.~n", [instance_name(), Id]),
    bmb_echo_client:start("echo", PID),
    PID.

%% @doc Message receiving loop.
%%
%%
loop(ThisClientId, UpLinkPID, ClientMap) ->

    % Receive message.
    receive
        % Message to register a child client.
        {register_client, ClientId, ClientPID} ->
            io:format("~s Register client:~p, PID=~p.~n",
                [instance_name(), ClientId, ClientPID]),
            NewClientMap = ClientMap#{ClientId => ClientPID},
            loop(ThisClientId, UpLinkPID, NewClientMap);

        % Forward message.
        {forward, SenderId, RecipientId, MsgString} ->
            io:format("~s forward from ~s to ~s:~p.~n",
                [instance_name(), SenderId, RecipientId, MsgString]),
            forward(SenderId, RecipientId, MsgString, ClientMap),
            loop(ThisClientId, UpLinkPID, ClientMap);

        % Send message UP.
        {client, SenderId, RecipientId, MsgString} ->
            io:format("~s from ~s to ~s:~p.~n",
                [instance_name(), SenderId, RecipientId, MsgString]),
            % TODO check if receipient is inside the domain
            UpLinkPID ! {client, ThisClientId++":"++SenderId, RecipientId, MsgString},
            loop(ThisClientId, UpLinkPID, ClientMap);

        % Unknown message.
        Msg ->
            io:format("~s Unknown message ~p.~n", [instance_name(), Msg]),
            loop(ThisClientId, UpLinkPID, ClientMap)

    end.

forward(SenderId, RecipientId, MsgString, ClientMap) ->
    case maps:find(RecipientId, ClientMap) of
        {ok, RecipientPID} -> RecipientPID ! {client, SenderId, RecipientId, MsgString};
        error -> error
    end.

