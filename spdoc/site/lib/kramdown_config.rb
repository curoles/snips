module KramdownConfig

def self.make(p)
    # Use kramdown as the markdown engine.
    p.set :markdown_engine, :kramdown
    
    # Configure kramdown
    # https://kramdown.gettalong.org/options.html
    #p.set :markdown
    
    # If you are using haml there can be issues with
    # automatic indentations, turning this off can help.
    p.set :haml, { ugly: true }
end

end
