% http://erlang.org/doc/design_principles/release_structure.html
% http://erlang.org/doc/design_principles/applications.html

{application, bumbler_app,
 [{description, "Bumbler Messenging Server"},
  {vsn, "1"},
  {modules, [bumbler_app, msg_server]},
  {registered, []},
  {applications, [kernel, stdlib, sasl]},
  {mod, {bumbler_app,[]}}
 ]}.
