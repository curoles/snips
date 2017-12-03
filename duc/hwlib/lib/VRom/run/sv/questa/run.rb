=begin rdoc
 Description::  VRom run script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

File.open('memory.txt', 'w') do |f|
  f << "00000000\n"
  f << "00000001\n"
  f << "00000010\n"
  f << "00000011\n"
  f << "00000100\n"
end

require File.join($module_attr[:src_root], 'hwlib', 'questa', 'sv_run')

