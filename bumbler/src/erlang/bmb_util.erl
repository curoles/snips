-module(bmb_util).
-author('Igor Lesik 2016').

-export([module_instance_name/1]).

module_instance_name(Module) ->
    string:left(Module++"["++pid_to_list(self())++"]", 32, $.).

