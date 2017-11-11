#!/usr/bin/env ruby
# http://www.rubydoc.info/gems/yard/file/docs/GettingStarted.md
# http://www.rubydoc.info/gems/yard/file/docs/Tags.md#taglist

require 'fileutils'
require 'etc'
require 'date'


module SPDoc

# Make a directory
#
# @param prefix [String] fixed path prefix
# @param path_components [Array<String>] parts of the directory path
# @param dry_run [Boolean] skip actual action if dry == true
# @return [String] directory path
#
def self.make_dir(prefix, path_components, dry_run: false)
    path = File.join(prefix, *path_components)
    puts "Making directory: #{path}"
    FileUtils.mkdir_p path unless dry_run
    path
end

# Make a file
#
# @param prefix [String] fixed path prefix
# @param path_components [Array<String>] parts of the directory path
# @param file_name [String] file name
# @param dry_run [Boolean] skip actual action if dry == true
# @return [String] file path
#
def self.make_file(prefix, path_components, file_name, dry_run: false)
    path = File.join(make_dir(prefix, path_components), file_name)
    puts "Making file: #{path}"
    FileUtils.touch path unless dry_run
    path
end

# CLI tool to create new SPDoc ticket.
# @author Igor Lesik 2017
#
class TicketTool

    class Ticket
        attr_accessor :user, :category, :title, :date

        def initialize
            @user = Etc.getlogin
            @category = 'task'
            @title = 'new_ticket'
            @date = Date.today
        end

        def prefix
            'site/source/pages/tickets'
        end

        def make_ticket_file
            path_parts = [category, date.year.to_s, user]
            file_name = "#{date.year}-#{date.month}-#{date.day}-#{title}.html.md.erb"
            SPDoc.make_file(prefix, path_parts, file_name, dry_run: true)
        end
    end

def ask_category(tkt)
    tkt
end

def ask_year(tkt)
    tkt
end

def ask_user_name(tkt)
    tkt
end

def ask_title(tkt)
    tkt
end

def run
    puts "HHi"
    tkt = ask_title ask_user_name ask_year ask_category Ticket.new
    tkt.make_ticket_file
end

end # class TicketTool

end # module SPDoc

tool = SPDoc::TicketTool.new
tool.run
