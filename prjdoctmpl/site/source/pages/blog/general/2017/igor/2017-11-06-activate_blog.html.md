---

title: Activate Blog
date: 2017/11/06
user: igor
category: general
tags:

---

# Activating blogging in SPD.

Based on [Middleman blogging](https://middlemanapp.com/basics/blogging/).

Added to config.rb:

```ruby
activate :blog do |blog|
  blog.prefix = "pages/blog"
  blog.sources = "{category}/{year}/{user}/{year}-{month}-{day}-{title}.html"
  blog.permalink = "{category}/{year}/{month}/{day}/{user}-{title}.html"
end
```

Manually created blog file:

```terminal
> mkdir -p site/source/pages/blog/general/2017/igor
> touch site/source/pages/blog/general/2017/igor/2017-11-06-activate_blog.html.md
```

Result page is at: `http://127.0.0.1:8000/pages/blog/general/2017/11/06/igor-activate_blog.html`

Note! HTTP server was started this way: `python3 -m http.server`

The blog page did not show fenced code properly. 
Blog [Activating Markdown](/pages/blog/general/2017/11/06/igor-activate_markdown.html)


TODO: enable [article generation](https://middlemanapp.com/basics/blogging/#generating-articles)
with `blog.new_article_template`.
