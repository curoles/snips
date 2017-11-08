module TicketsActivator

def self.activate(cfg)
cfg.activate :blog do |blog|
  blog.prefix = "pages/tikets"
  blog.layout = "blog/layout"
  blog.sources = "{category}/{year}/{user}/{year}-{month}-{day}-{title}.html"
  blog.permalink = "permalink/{category}/{year}/{month}/{day}/{user}-{title}.html"
  blog.paginate = true
  blog.per_page = 20
  blog.tag_template = "pages/blog/tag.html"
  blog.calendar_template = "pages/blog/calendar.html"
end

end

end
