module RedcarpetConfig

def self.make(p)
    # Use redcarpet as the markdown engine.
    p.set :markdown_engine, :redcarpet # default is :kramdown
    
    # Configure redcarpet to use Github style fenced code blocks
    # (tripe back ticks ```) to denote code.
    p.set :markdown, :fenced_code_blocks => true, :smartypants => true, :tables => true,
                   :footnotes => true, :highlight => true, :with_toc_data => true,
                   :no_intra_emphasis => true
    
    # If you are using haml there can be issues with
    # automatic indentations, turning this off can help.
    p.set :haml, { ugly: true }
end

end
