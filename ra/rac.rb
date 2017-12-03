#!/usr/bin/env ruby
#
# To change Ruby version env points to on Ubuntu:
# sudo update-alternatives --set ruby /usr/bin/ruby1.9.1

=begin
author: Igor Lesik 2013
brief:  Run Ra Language Ruby compiler
=end

require_relative 'ra_compiler'

prog_name = ARGV[0]
out_dir = ARGV[1]
load prog_name

Compiler.new(out_dir).compile(prog)
