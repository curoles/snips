#!/usr/bin/env ruby
# http://www.rubydoc.info/gems/yard/file/docs/GettingStarted.md
# http://www.rubydoc.info/gems/yard/file/docs/Tags.md#taglist

module SPDoc

# CLI tool to create new SPDoc ticket.
# @author Igor Lesik 2017
#
class TicketTool

class Ticket
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
    ask_title ask_user_name ask_year ask_category Ticket.new
end

end # class TicketTool

end # module SPDoc

tool = SPDoc::TicketTool.new
tool.run
