# TextParse

[![Tests Status](https://travis-ci.org/JuliaComputing/TextParse.jl.svg?branch=master)](https://travis-ci.org/JuliaComputing/TextParse.jl?branch=master) [![Coverage Status](https://coveralls.io/repos/github/JuliaComputing/TextParse.jl/badge.svg?branch=master)](https://coveralls.io/github/JuliaComputing/TextParse.jl?branch=master)

TextParse uses Julia's generated functions to generate efficient specialized parsers for text files. Right now, there is a good set of features for reading CSV files (see [the documentation](https://JuliaComputing.github.io/TextParse.jl/stable)). Parsing packages can use TextParse as a framework for implementing parsers for other formats.

## Related package
- [CSV.jl](https://github.com/JuliaData/CSV.jl) - Package for reading CSV files into [DataStreams](https://github.com/JuliaData/DataStreams.jl) API. It loads the data into a `DataFrame`. TextParse tries to be minimal and returns a tuple of vectors as the output of `csvread` and adds useful features such as parsing string columns as PooledArrays.


[![](https://img.shields.io/badge/docs-stable-blue.svg)](https://JuliaComputing.github.io/TextParse.jl/stable)
[![](https://img.shields.io/badge/docs-latest-blue.svg)](https://JuliaComputing.github.io/TextParse.jl/latest)
