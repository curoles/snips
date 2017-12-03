%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc
%% Bumbler App starts Bumbler Messaging Server.
%%
-module(bumbler_app).
-behaviour(application).

-export([start/2, stop/1]).

instance_name() ->
    bmb_util:module_instance_name("App").

start(_Type, _Args) ->
    ServerPID = spawn(fun bmb_msg_server:loop/0),
    register(server_process, ServerPID),
    io:format("~s Bumbler server loop sarted PID=~p ~n",
        [instance_name(), ServerPID]),
    %bmb_msg_gate:send(ServerPID, 0, 1, "say true"),
    GateFactoryPID = spawn(fun bmb_gate_factory:loop/0),
    io:format("~s Gate Factory created PID=~p.~n",
        [instance_name(), GateFactoryPID]),
    GateFactoryPID ! new, % new Gate
    %timer:sleep(100),
    %msg_gate_process ! {client, 0, 1, "say true"},
    create_default_modules(),
    {ok, self()}. %ch_sup:start_link().

stop(_State) ->
    ok.

%% @doc Returns resource/client Id as string.
%%
%format_client_id_string(PathList) ->
%    string:join(PathList,":") ++ "@" ++ net_adm:localhost().


create_default_modules() ->
    InternalDomainId = "internal", %format_client_id_string(["internal"]),
    InternalDomainPID = bmb_internal_domain:start(InternalDomainId, msg_gate_process),
    msg_gate_process ! {register_domain, InternalDomainId, InternalDomainPID},
    TcpDomainId = "tcp",
    TcpDomainPID = bmb_tcp_domain:start(TcpDomainId, msg_gate_process),
    msg_gate_process ! {register_domain, TcpDomainId, TcpDomainPID},

    %_BotDomainPID = spawn(bmb_bot_domain, loop/1, [_InternalDomainPID]),
    %_InternalDomainPID ! {register_child, _BotDomainPID, [internal, bot]},
    ok.
