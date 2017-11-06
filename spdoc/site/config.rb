# @igor Do not strip index.html from path.
set :strip_index_file, false

ignore '**/*.swp' # @igor ignore VIM temporary files

# Activate and configure extensions
# https://middlemanapp.com/advanced/configuration/#configuring-extensions

activate :autoprefixer do |prefix|
  prefix.browsers = "last 2 versions"
end

activate :blog do |blog|
  blog.prefix = "pages/blog"
  blog.sources = "{category}/{year}/{user}/{year}-{month}-{day}-{title}.html"
  blog.permalink = "{category}/{year}/{month}/{day}/{user}-{title}.html"
end

# Activate middleman-syntax and enable line numbers.
# Note line numbers can be disabled on a per block basis
# e.g. ```ruby?line_numbers=false
activate :syntax, :line_numbers => true
# Use redcarpet as the markdown engine.
set :markdown_engine, :redcarpet # default is :kramdown
# configure redcarpet to use github style fenced code blocks
# (tripe back ticks ```) to denote code
set :markdown, :fenced_code_blocks => true, :smartypants => true
# if you are using haml there can be issues with
# automatic indentations, turning this off can help
set :haml, { ugly: true }

# Layouts
# https://middlemanapp.com/basics/layouts/

# Per-page layout changes
page '/*.xml', layout: false
page '/*.json', layout: false
page '/*.txt', layout: false

# Activate Bootstrap Helpers
activate :bh

# With alternative layout
# page '/path/to/file.html', layout: 'other_layout'

# Proxy pages
# https://middlemanapp.com/advanced/dynamic-pages/

# proxy(
#   '/this-page-has-no-template.html',
#   '/template-file.html',
#   locals: {
#     which_fake_page: 'Rendering a fake page with a local variable'
#   },
# )

# Helpers
# Methods defined in the helpers block are available in templates
# https://middlemanapp.com/basics/helper-methods/

# helpers do
#   def some_helper
#     'Helping'
#   end
# end

# Build-specific configuration
# https://middlemanapp.com/advanced/configuration/#environment-specific-settings

# configure :build do
#   activate :minify_css
#   activate :minify_javascript
# end
