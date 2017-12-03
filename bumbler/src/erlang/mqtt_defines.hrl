%% @author    Igor Lesik.
%% @copyright Igor Lesik 2016.
%%
%% @doc MQTT definitions.
%%
%% @see http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/os/mqtt-v3.1.1-os.html
%%
%% It is NOT -module(mqtt_defines).

%% @doc TCP ports.
%% TCP ports 8883 and 1883 are registered with IANA for MQTT TLS and non TLS communication respectively.
%% http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/os/mqtt-v3.1.1-os.html#_Toc398718098
%%
-define(MQTT_TCP_PORT, 1883).
-define(MQTT_TCP_TLS_PORT, 8883).
