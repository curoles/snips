---

title: Make Ticket maker 
date: 2017/11/10
user: igor
category: task
status: closed
progress: 100
tags: priority-high, tickets, tools
assignee: igor

---

# Make Ticket maker CLI tool


I am tired of creating Ticket files manually, time to automate this procedure
and make CLI tool for that.

Here is a flowchart of how such tool should work:

<pre><img src='https://g.gravizo.com/svg?
@startuml;
(*) --> "analyze cmd line options" as analyze_opts;

analyze_opts --> "ask category" as ask_category;
ask_category  -> "ask user name" as ask_user_name;
ask_user_name -> "ask ticket title" as ask_title;

ask_title --> "analyze params" as analyze_params;

analyze_params --> if "accept parameters?" then;
  -->[yes] "write ticket file" as write_ticket_file;
else;
  -->[no] ask_category;
endif;

write_ticket_file --> (*);
@enduml
'></pre>


Functions can be called pipe style taking and returning Ticket object:

```ruby
class TicketTool

    class Ticket
    end
    
    def ask_category(tkt)
        tkt
    end
    
    def ask_user_name(tkt)
        tkt
    end
    
    // ...
    
    def run
        ask_title ask_user_name ask_category Ticket.new
    end
```

---
Sequence diagram (with js-sequence-diagrams)

<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.2.1/jquery.min.js"></script>
<script src="https://bramp.github.io/js-sequence-diagrams/js/webfont.js"></script>
<script src="https://bramp.github.io/js-sequence-diagrams/js/snap.svg-min.js"></script>
<script src="https://bramp.github.io/js-sequence-diagrams/js/underscore-min.js"></script>
<script src="https://bramp.github.io/js-sequence-diagrams/js/sequence-diagram-min.js"></script>


<pre><div class="diagram">
Tool->User: category? default=task
User-->>Tool: bug
Tool->User: user? default=current user
User-->>Tool: igor
Tool->User: title? default=
User-->>Tool: my_ticket
Tool->User: Check {task, igor, my_ticket}
Tool->User: Accept?
Note over User: dude is thinking
User-->>Tool: yes
Tool->OS: write into new ticket file
</div></pre>
<script>
$(".diagram").sequenceDiagram({theme: 'hand'});
</script>

---

2017/11/12 All is coded.

```ruby
#!/usr/bin/env ruby
# http://www.rubydoc.info/gems/yard/file/docs/GettingStarted.md
# http://www.rubydoc.info/gems/yard/file/docs/Tags.md#taglist

require 'fileutils'
require 'etc'
require 'date'
require 'highline/import'
require 'optparse'

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
    puts "Making(#{!dry_run}) directory: #{path}"
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
    path = File.join(make_dir(prefix, path_components, dry_run: dry_run), file_name)
    puts "Making(#{!dry_run}) file: #{path}"
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
            options = {}
        end

        def make_ticket_file(dry_run: false)
            path_parts = [category, date.year.to_s, user]
            file_name = "#{date.year}-#{date.month}-#{date.day}-#{title}.html.md.erb"
            path = SPDoc.make_file(prefix, path_parts, file_name, dry_run: dry_run)
            File.write(path, text) unless dry_run
        end

        def text
%{
---

title: #{@title}
date: #{@date.strftime('%Y/%m/%d')}
user: #{@user}
category: #{@category}
status: open
progress: 0
tags: priority-medium
assignee: #{@user}

---

# #{@title}
}
        end

    end


    def initialize
        # Command line options, mostly parameters of the ticket.
        @options = {}
    end

    # Parse command line options.
    def parse_options
        OptionParser.new do |opts|
          opts.banner = "Usage: spdoc-ticket.rb [--category] [--user] [--title]"
    
          opts.on("-uNAME", "--user=NAME", "Author of this ticket") do |name|
              @options[:user] = name
          end 
          opts.on("-cNAME", "--category=NAME", "Category of the ticket (task, bug, review  and etc.)") do |name|
              @options[:category] = name
          end
          opts.on("-tTITLE", "--title=TITLE", "Title of the ticket") do |title|
              @options[:title] = title
          end
    
          opts.on("-h", "--help", "Prints this help") do
              puts opts
              exit
          end    
        end.parse!
    end

    def ask_category(tkt)
        tkt.category =
        if @options[:category] then  @options[:category]
        else ask("Category(task, bug and etc)?  ") { |q| q.default = "task" } end
        tkt
    end


    def ask_user_name(tkt)
        tkt.user =
        if @options[:user] then @options[:user]
        else ask("User?  ") { |q| q.default = Etc.getlogin } end
        tkt
    end

    def ask_title(tkt)
        tkt.title =
        if @options[:title] then @options[:title].strip.gsub(/\s/,'_')
        else ask("Title?  ") { |q| q.validate = /\A\S+\Z/ } end
        tkt
    end

    def run
        parse_options
        user_accept = true
        begin
            if !user_accept and !agree('Continue (otherwise exit) ? ') then exit end
            tkt = ask_title ask_user_name ask_category Ticket.new
            tkt.make_ticket_file(dry_run: true)
        end until user_accept = agree('Do you like it? Create the ticket? ')
        tkt.make_ticket_file(dry_run: false)
    end


end # class TicketTool

end # module SPDoc

tool = SPDoc::TicketTool.new
tool.run
```
