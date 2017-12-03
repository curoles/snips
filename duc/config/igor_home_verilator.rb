
=begin rdoc
 Description::  Environment description.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

module DucCustomConfiguration

@@ruby = {
  :path => '/usr/bin/ruby',
  :options => '-W2'
}

@@verify = {
  :lang  => 'v',
  :vlang => 'v',
}

@@verilator = {}
@@verilator[:bin]  = "/usr/local/bin"
@@verilator[:vlog] = "#{@@verilator[:bin]}/verilator"
 
@@tool = {
  :type  => 'verilator',
  :vlog  => @@verilator[:vlog]
}

@@work = {
  :base => '/home/igor/prj/github/duc/work'
}
@@work[:build] = "#{@@work[:base]}/build"
@@work[:run]   = "#{@@work[:base]}/run"

end #module
