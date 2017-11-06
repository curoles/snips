---

title: Activate Markdown
date: 2017/11/06
user: igor
category: general
tags:

---

# Activating Markdown extention

Resourses:

- https://middlemanapp.com/basics/template-engine-options
- http://weaver.tech/blog/code-highlighting-in-middleman.html
- https://github.com/middleman/middleman-syntax
- https://github.com/adam-p/markdown-here/wiki/Markdown-Cheatsheet


The very first blog page did not show fenced code properly. So I added 
`gem 'middleman-syntax'` to Gemfile and run `bundle install`.
Then added `activate :syntax, :line_numbers => true` to config.rb.


And it did not work. So I added `gem 'redcarpet'` to Gemfile and
to config.rb added

```ruby
set :markdown_engine, :redcarpet
set :markdown, :fenced_code_blocks => true
```
and it worked.


But I do not see syntax highlighting. Just in case checked that
https://github.com/jneen/rouge/wiki/List-of-supported-languages-and-lexers
has ruby, it does.


https://github.com/middleman/middleman-syntax says:

> On a default (i.e. unstyled) Middleman project, it will appear
> as if middleman-syntax isn't working, since obviously no CSS
> has been applied to color your code.

Created file source/stylesheets/highlighting.css.erb:

```erb
<%= Rouge::Themes::Github.render(:scope => '.highlight') %>
```

At the top of source/stylesheets/site.css.scss placed :

```css
@import 'highlighting.css';
```
