---

title: Make Ticket maker 
date: 2017/11/10
user: igor
category: task
status: open
progress: 10
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

