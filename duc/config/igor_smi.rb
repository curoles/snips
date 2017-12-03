
=begin rdoc
 Description::  Environment description.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

module DucCustomConfiguration

@@ruby = {
  :path => '/tools/local/ruby/bin/ruby',
  :options => '-W2'
}

@@verify = {
  :lang  => 'v',
  :vlang => 'sv',
}

@@questa = {}
@@questa[:version] = '10.3'
@@questa[:base   ] = '/tools/mentor/questa'
@@questa[:home   ] = "#{@@questa[:base]}/#{@@questa[:version]}/questasim"
@@questa[:bin    ] = "#{@@questa[:home]}/linux_x86_64"
@@questa[:vlog   ] = "#{@@questa[:bin]}/vlog"
@@questa[:vsim   ] = "#{@@questa[:bin]}/vsim"
@@questa[:vlib   ] = "#{@@questa[:bin]}/vlib"
@@questa[:vopt   ] = "#{@@questa[:bin]}/vopt"
@@questa[:license] = '1717@sv1.smi.local:1717@sv3.smi.local:1717@sv4.smi.local:1717@login1.smi.local:1717@sge1.smi.local'
 
@@tool = {
  :type  => 'questa',
  :vlog  => @@questa[:vlog],
  :vsim  => @@questa[:vsim],
  :vlib  => @@questa[:vlib],
  :vopt  => @@questa[:vopt]
}

# LM_LICENSE_FILE=5280@sv3.smi.local /tools/cadence/RC/RC-13.11/bin/rc
@@cadence_rtlcomp = {
  :license => '5280@sv3.smi.local',
  :version => '13.11',
  :base    => '/tools/cadence/RC'
}
@@cadence_rtlcomp[:home] = "#{@@cadence_rtlcomp[:base]}/RC-#{@@cadence_rtlcomp[:version]}"
@@cadence_rtlcomp[:bin] = "#{@@cadence_rtlcomp[:home]}/bin"
@@cadence_rtlcomp[:rc] = "#{@@cadence_rtlcomp[:home]}/rc"

@@work = {
  :base => '/local_disk/igor/duc'
}
@@work[:build] = "#{@@work[:base]}/build"
@@work[:run]   = "#{@@work[:base]}/run"

end #module
