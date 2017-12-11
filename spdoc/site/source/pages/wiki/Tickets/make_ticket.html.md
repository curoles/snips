# How To Make Ticket

The easiest way to make Ticket is to use tool called
`spdoc-ticket.rb` that resides in `tools` directory.

## Built in help

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

`spdoc-ticket.rb` uses `highline` gem, if it is not install you
may see following error:

```
in `require': cannot load such file -- highline/import
```

In this case install `highline`:

```
$ sudo gem install highline
```

# Example of making a ticket

```
spdoc$ tools/spdoc-ticket.rb
Category(task, bug and etc)?  |task|  task
User?  |igor|  igor
Title?  Make support for non-blog resources like wiki pages
Your answer isn't valid (must match /\A\S+\Z/).
?  Make_support_for_non_blog_resources_like_wiki_pages
Making(false) directory: tools/../site/source/pages/tickets/task/2017/igor
Making(false) file: tools/../site/source/pages/tickets/task/2017/igor/2017-12-10-Make_support_for_non_blog_resources_like_wiki_pages.html.md.erb
Do you like it? Create the ticket? yes
Making(true) directory: tools/../site/source/pages/tickets/task/2017/igor
Making(true) file: tools/../site/source/pages/tickets/task/2017/igor/2017-12-10-Make_support_for_non_blog_resources_like_wiki_pages.html.md.erb
igor@smidev1:~/prj/github/snips/snips/spdoc$ ls site/source/pages/tickets/task/2017/igor/2017-12-10-Make_support_for_non_blog_resources_like_wiki_pages.html.md.erb
site/source/pages/tickets/task/2017/igor/2017-12-10-Make_support_for_non_blog_resources_like_wiki_pages.html.md.erb
igor@smidev1:~/prj/github/snips/snips/spdoc$ 
igor@smidev1:~/prj/github/snips/snips/spdoc$ cat site/source/pages/tickets/task/2017/igor/2017-12-10-Make_support_for_non_blog_resources_like_wiki_pages.html.md.erb

---

title: Make_support_for_non_blog_resources_like_wiki_pages
date: 2017/12/10
user: igor
category: task
status: open
progress: 0
tags: priority-medium
assignee: igor

---

# Make_support_for_non_blog_resources_like_wiki_pages
```

