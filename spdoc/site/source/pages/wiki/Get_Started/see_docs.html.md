---
title: How to see your documentation with Web browser
---

Once .html files are created you can see them locally
in your Web browser by running a web-server.

One easy and usually right away available method is to
use Python simple HTTP server. `cd` into `build/website`
directory and run `python -m SimpleHTTPServer 8000` or
`python3 -m http.server`.
If server is runnning you should something like this:

```
build$ cd website
build/website$ python -m SimpleHTTPServer 8000
Serving HTTP on 0.0.0.0 port 8000 ...
``` 

Now open your Web browser and type URL `http://127.0.0.1:8000`.
