#!/usr/bin/ruby

#author Igor Lesik 2013


require 'ostruct'
require 'mysql2'
require 'highline/import'

puts "Press Ctrl-D at any time to abort"

mysql_user = ask("Enter your MySQL user name:  ") { |q| q.default = "root" }
mysql_pswd = ask("Enter your MySQL password:   ") { |q| q.echo = "x" }

Sql = Mysql2::Client.new(
  :host => "localhost",
  :username => mysql_user,
  :password => mysql_pswd,
  :database => 'podb'
)

def title(msg)
  say "\n<%= color('#{msg}', BOLD) %>"
end

def query_people
  people = Sql.query("SELECT * FROM person")
  people.each do |person|
    puts person
  end
end

def create_person
  #name = ask("Orderer Name?  (last, first)  ") { |q| q.validate = /\A\w+, ?\w+\Z/ }
  first_name = ask("First name? ") { |q| q.validate = /\A\w+\Z/ }
  last_name = ask("Last name? ") { |q| q.validate = /\A\w+\Z/ }
  phone = ask("Phone? ") { |q| } #q.validate = /\A\w+\Z/ }
  email = ask("email? ") { |q| q.default = 'no@email.com'; q.validate = /\A\w+@\w+\.\w+\Z/ }

  Sql.query(
    "INSERT INTO person(first_name, last_name, phone, email) \
     VALUES('#{first_name}', '#{last_name}', '#{phone}', '#{email}')"
  )
end

def query_project
  projects = Sql.query("SELECT * FROM project")
  projects.each do |project|
    puts project
  end
end

def create_project
  name = ask("Project/Department Name? ") #{ |q| q.validate = /\A\w+, ?\w+\Z/ }
  manager = ask("Manager?  (first, last)  ") { |q| q.validate = /\A\w+, ?\w+\Z/ }
  manager_first_name = manager[/\A\w+/]
  manager_last_name = manager[/, ?\w+\Z/][/\w+/]

  person = Sql.query(
    "SELECT * FROM person WHERE first_name='#{manager_first_name}'"
  )

  person.each do |p|
    puts p
  end

  if person.count < 1
    say "No person with name #{manager} exists"
  else
    person_id = person.first['id']
    say "Found person #{manager} with id #{person_id}"
    Sql.query(
      "INSERT INTO project(name, manager) VALUES('#{name}', #{person_id})"
    )
  end
end

def query_source
  sources = Sql.query("SELECT * FROM source")
  sources.each do |source|
    puts source
  end
end

def create_source
  name = ask("Source Name? ")
  addr = ask("Address? ")
  info = ask("Contact info? ")
  Sql.query(
    "INSERT INTO source(name, address, contacts) VALUES('#{name}', '#{addr}', '#{info}')"
  )
end

def query_item_type
  types = Sql.query("SELECT * FROM item_type")
  types.each do |type|
    puts type
  end
end

def create_item_type
  name = ask("Item Name? ")
  descr = ask("Description? ")
  #choose do |menu|
  #  menu.prompt = "Is asset?  "
  #  menu.choice(:YES) { PO.asset = 'YES' }
  #  menu.choice(:NO)  { PO.asset = 'NO'  }
  #  #menu.choices(:YES, :NO) { say("Not from around here, are you?") }
  #end
  #asset
  Sql.query(
    "INSERT INTO item_type(name, description) VALUES('#{name}', '#{descr}')"
  )
end

def show_po(po)
  po_print = <<POINFO

PURCHASE ORDER DETAILS
----------------------
Id      : #{po.id}
Date    : #{po.date}
Orderer : #{po.orderer}
Asset   : #{po.asset}

POINFO

  puts po_print
end

def create_po
 
  #begin

  po = OpenStruct.new
  po.id = ask("PO Id:  ") { |q| q.default = 'PO-' + DateTime.now.to_date.to_s }
  #po.orderer = ask("Orderer Name?  (last, first)  ") { |q| q.validate = /\A\w+, ?\w+\Z/ }

  #show_po(po)
  #do_again = ask changes?
  do_changes = false
  choose do |menu|
    menu.prompt = "Want to make changes?  "
    menu.choice(:YES) { do_changes = true  }
    menu.choice(:NO)  { do_changes = false }
  end
 
  #end while do_changes

  po.date = DateTime.now.to_date.to_s

  Sql.query(
  "INSERT INTO po(id_string, date_created) VALUES('#{po.id}', '#{po.date}')")

   #ask("Interests?  (comma sep list)  ",lambda { |str| str.split(/,\s*/) })

end

def ask_query
  title("Select object to query about:")
  choose do |menu|
    menu.prompt = "What would you like to see?  "
    menu.choice('people')    { query_people  }
    menu.choice('project')   { query_project }
    menu.choice('source')    { query_source  }
    menu.choice('item type') { query_item_type }
    menu.choice('item')      {  }
    menu.choice('payment type'){  }
    menu.choice('PO')        {  }

    menu.default = 'people'
  end
end

def ask_create
  title("Select object to be created:")
  choose do |menu|
    menu.prompt = "What would you like to create?  "
    menu.choice('person')    { create_person  }
    menu.choice('project')   { create_project }
    menu.choice('source')    { create_source  }
    menu.choice('item type') { create_item_type }
    menu.choice('item')      {  }
    menu.choice('payment type'){  }
    menu.choice('PO')        { create_po }

    menu.default = 'person'
  end
end

def ask_query_or_quit
  quit = false
  title("Select action:")
  choose do |menu|
    menu.prompt = "What would you like to do?  "
    menu.choice(:query)  { ask_query  }
    menu.choice(:create) { ask_create }
    #menu.choice(:remove) { ask_remove }
    menu.choice(:quit)   { quit = true; say("EXIT") }
    menu.default = :query
  end
  !quit
end

while ask_query_or_quit do
end

