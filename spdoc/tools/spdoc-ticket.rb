#!/usr/bin/env ruby
# http://www.rubydoc.info/gems/yard/file/docs/GettingStarted.md
# http://www.rubydoc.info/gems/yard/file/docs/Tags.md#taglist

require 'fileutils'
require 'etc'
require 'date'
require 'highline/import'

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
        attr_accessor :user, :category, :title, :date, :prefix

        def initialize
            @user = Etc.getlogin
            @category = 'task'
            @title = 'new_ticket'
            @date = Date.today
            @prefix = File.join(File.dirname(__FILE__), '..','site','source','pages','tickets')
            if not File.exist? @prefix then
                raise ArgumentError, "Directory #{@prefix} does not exist"
            end
        end

        def make_ticket_file
            path_parts = [category, date.year.to_s, user]
            file_name = "#{date.year}-#{date.month}-#{date.day}-#{title}.html.md.erb"
            SPDoc.make_file(prefix, path_parts, file_name, dry_run: true)
        end
    end

    def ask_category(tkt)
        tkt.category = ask("Category(task, bug and etc)?  ") { |q| q.default = "task" }
        tkt
    end


    def ask_user_name(tkt)
        tkt.user = ask("User?  ") { |q| q.default = Etc.getlogin }
        tkt
    end

    def ask_title(tkt)
        tkt.title = ask("Title?  ") { |q| q.validate = /\A\S+\Z/ }
        tkt
    end

    def run
        tkt = ask_title ask_user_name ask_category Ticket.new
        tkt.make_ticket_file
    end

end # class TicketTool

end # module SPDoc

tool = SPDoc::TicketTool.new
tool.run
