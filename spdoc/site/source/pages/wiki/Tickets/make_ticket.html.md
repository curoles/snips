---
title: Make New Ticket
---

# How To Make New Ticket

The easiest way to make Ticket is to use interactive tool called
`spdoc-ticket.rb` that resides in `tools` directory.
You, of course, can always create new ticket file manually
by following predefined rules how file name should look like.

## Ticket File

Ticket pages are blog pages. Each ticket is one blog post.
Ticket file path and naming convention are:


```
site/source/pages/ticket/category/year/user/year-month-day-tiket_title.html.md.erb
```

## spdoc-ticket.rb built in help

To see `spdoc-ticket.rb` built-in help type:

```terminal
spdoc$ tools/spdoc-ticket.rb --help
```

You should see something like this:

```terminal
spdoc$ tools/spdoc-ticket.rb --help 
Usage: spdoc-ticket.rb [--category] [--user] [--title]
    -u, --user=NAME                  Author of this ticket
    -c, --category=NAME              Category of the ticket (task, bug, review  and etc.)
    -t, --title=TITLE                Title of the ticket
    -h, --help                       Prints this help
```

`spdoc-ticket.rb` uses `highline` gem, if it is not installed then you
may see following error:

```
in `require': cannot load such file -- highline/import
```

In this case install `highline`:

```
$ sudo gem install highline
```

# Example of making a ticket

Interactive terminal session:


```terminal
spdoc$ tools/spdoc-ticket.rb 
Category(task, bug and etc)?  |task|  task
User?  |igor|  
Title?  Install common javascripts to use SPDoc offline
Making(false) directory: tools/../site/source/pages/tickets/task/2017/igor
Making(false) file: tools/../site/source/pages/tickets/task/2017/igor/2017-12-14-Install_common_javascripts_to_use_SPDoc_offline.html.md.erb
Do you like it? Create the ticket? yes
Making(true) directory: tools/../site/source/pages/tickets/task/2017/igor
Making(true) file: tools/../site/source/pages/tickets/task/2017/igor/2017-12-14-Install_common_javascripts_to_use_SPDoc_offline.html.md.erb
```

Generated file:


```
---

title: Install common javascripts to use SPDoc offline
date: 2017/12/14
user: igor
category: task
status: open
progress: 0
tags: priority-medium
assignee: igor

---

# Install common javascripts to use SPDoc offline
```

