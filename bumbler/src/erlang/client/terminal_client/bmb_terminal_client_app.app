% http://erlang.org/doc/design_principles/release_structure.html
% http://erlang.org/doc/design_principles/applications.html

{application, bmb_terminal_client_app,
 [{description, "Bumbler Erlang Node Terminal Messenger"},
  {vsn, "1"},
  {modules, [bmb_terminal_client_app, bmb_terminal_client]},
  {registered, []},
  {applications, [kernel, stdlib, sasl]},
  {mod, {bmb_terminal_client_app,[]}}
 ]}.
