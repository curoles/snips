---
title: Build SPDoc own documentation
---

# Build Documentation for SPDoc project

SPDoc project itself uses SPDoc do document the project.
In order to see how SPDoc project documentation is rendered into HTML
you need to compile .md files into .html files.

First, create a build directory somewhere outside of the SPDoc
source directory.

```terminal
~/a$ mkdir build
```

Change directory into the newly created build directory.

```terminal
~/a$ cd build
~/a/build$
```

Configure build scripts inside the build directory by calling configuration
script located in the source directory.

```terminal
~/a/build$ bash <path to spdoc source>/configure.bash
```
In case some nessary tools are missing, configure.bash will inform about it.
Please install missing tools before and repeat the procedure by running
`configure.bash` again.

For example, you may see a message like this if `middleman` is not installed:

```terminal
User                       : igor
Current working directory  : /home/igor/prj/github/snips/build_spdoc
Path to source files       : ../snips/spdoc
Abs path to source files   : /home/igor/prj/github/snips/snips/spdoc
Ruby version               : ruby 2.3.3p222 (2016-11-21) [i386-linux-gnu]
Gem version                : 2.5.2
***Error: Middleman gem is not installed. Do 'sudo gem install middleman'
Note: you may need to install ruby-dev package, sudo apt-get install ruby-all-dev
```

The last step of building the .html documentation files is to call `make` inside
the build directory. However, if during the build some ruby gems are reported
to be missing, you need to install them. See section [Other known issues](#knownIssues).

`make` command calls `middleman` that creates static .html pages.
Once `make` is finished you should see directory called `website` inside the build
directory.
`website` directory will have all generated .html files inside, together with required
CSS and JavaScript files.

```terminal
build$ ls
config.makefile  igor.config.makefile  Makefile  website
igor@smidev1:~/prj/github/snips/build_spdoc$ ls website/
images  index.html  javascripts  pages  stylesheets
```

## Other known issues with tools {#knownIssues}

### Could not find minitest-5.10.3 in any of the sources

```terminal
$ make
cd ../snips/spdoc/site && NO_CONTRACTS=true bundle exec middleman build --clean --verbose --build-dir=/home/igor/prj/github/snips/build_spdoc/website
Could not find minitest-5.10.3 in any of the sources
Run `bundle install` to install missing gems.
../snips/spdoc/build/build.makefile:13: recipe for target 'build_site' failed
make: *** [build_site] Error 7
```

#### Solution is to install missing gems by running `bundle install`

To install missing required gems `cd` into SPDoc source directory,
then `cd` into `site` subdirectory and do `bundle install`.

```terminal
spdoc$ cd site
spdoc/site$ bundle install
Fetching gem metadata from https://rubygems.org/............
Using concurrent-ruby 1.0.5
Using i18n 0.7.0
Fetching minitest 5.10.3
...
```

### ExecJS::RuntimeUnavailable: Could not find a JavaScript runtime.

```terminal
$ make
cd ../snips/spdoc/site && NO_CONTRACTS=true bundle exec middleman build --clean --verbose --build-dir=/home/igor/prj/github/snips/build_spdoc/website
bundler: failed to load command: middleman (/usr/local/bin/middleman)
ExecJS::RuntimeUnavailable: Could not find a JavaScript runtime. See https://github.com/rails/execjs for a list of available runtimes.
...
```

#### Solution is to install Node.js.

```terminal
> sudo apt-get install nodejs
```
