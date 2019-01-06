@inline function eatwhitespaces(str::Union{VectorBackedUTF8String, String}, i=1, len=lastindex(str))
    while i<=len
        @inbounds b = codeunit(str, i)

        if b==0x20 # This is ' '
            i += 1
        else
            break
        end
    end
    return i
end

@inline function eatnewlines(str::Union{VectorBackedUTF8String, String}, i=1, len=lastindex(str))
    count = 0
    while i<=len
        @inbounds b = codeunit(str, i)
        if b == 0xd # '\r'
            i += 1
            if i<=len
                @inbounds b = codeunit(str, i)
                if b == 0xa # '\n'
                    i += 1
                end
            end
            count += 1
        elseif b == 0xa
            i += 1
            if i<=len
                @inbounds b = codeunit(str, i)
                if b == 0xd
                    i += 1
                end
            end
            count += 1
        else
            break
        end
    end

    return i, count
end

@inline function tryparsenext_base10_digit(T,str::Union{VectorBackedUTF8String, String},i, len)
    i > len && @goto error
    @inbounds b = codeunit(str,i)
    diff = b-0x30
    diff >= UInt8(10) && @goto error
    return convert(T, diff), i+1

    @label error
    return nothing
end

@inline _isdigit(b::UInt8) = ( (0x30 ≤ b) & (b ≤ 0x39) )

@inline function parse_uint_and_stop(str::Union{VectorBackedUTF8String, String}, i, len, n::T) where {T <: Integer}
    ten = T(10)
    # specialize handling of the first digit so we can return an error
    max_without_overflow = div(typemax(T)-9,10) # the larg
    i <= len || return n, false, i
    @inbounds b = codeunit(str, i)
    diff = b-0x30
    if diff < UInt8(10) && n <= max_without_overflow
        n *= ten
        n += T(diff)
    else
        return n, false, i
    end
    i += 1

    while i <= len && n <= max_without_overflow
        @inbounds b = codeunit(str, i)
        diff = b-0x30
        if diff < UInt8(10)
            n *= ten
            n += T(diff)
        else
            return n, true, i
        end
        i += 1
    end
    return n, true, i
end

@inline function read_digits(str::Union{VectorBackedUTF8String, String}, i, len)
    # slurp up extra digits
    while i <= len
        @inbounds b = codeunit(str, i)
        if !_isdigit(b) # do nothing
            return i
        end
        i += 1
    end
    return i
end

@inline function _is_e(str::Union{VectorBackedUTF8String, String}, i)
    @inbounds b = codeunit(str, i)
    return  (b==0x65) | (b==0x45)
end

@inline function _is_negative(str::Union{VectorBackedUTF8String, String}, i)
    @inbounds b = codeunit(str, i)
    return b==0x2d
end

@inline function _is_positive(str::Union{VectorBackedUTF8String, String}, i)
    @inbounds b = codeunit(str, i)
    return b==0x2b
end

const pre_comp_exp = Float64[10.0^i for i=0:22]

@inline function tryparsenext(::Numeric{F}, str::Union{VectorBackedUTF8String, String}, i, len) where {F<:AbstractFloat}
    R = Nullable{F}

    i>len && @goto error

    negate = false
    @inbounds b = codeunit(str, i)
    if b==0x2d # '-'
        negate = true
        i += 1
    elseif b==0x2b # '+'
        i +=1
    end

    f1::Int64 = 0

    # read an integer up to the decimal point
    f1, rval1, idecpt = parse_uint_and_stop(str, i, len, f1)
    idecpt = read_digits(str, idecpt, len) # get any trailing digits
    i = idecpt

    ie = i
    frac_digits = 0

    # next thing must be dec pt.
    if i <= len && @inbounds(codeunit(str, i)) == 0x2e # Check for '.'
        i += 1
        f1, rval2, ie = parse_uint_and_stop(str, i, len, f1)
        frac_digits = ie - i

        ie = read_digits(str, ie, len) # get any trailing digits
    elseif !rval1 # no first number, and now no deciaml point => invalid
        @goto error
    end

    # Next thing must be exponent
    i = ie
    eval::Int32 = 0

    if i <= len && _is_e(str, i)
        i += 1

        enegate = false
        if i<=len
            if _is_negative(str, i)
                enegate = true
                i += 1
            elseif _is_positive(str, i)
                i += 1
            end
        end
        eval, rval3, i = parse_uint_and_stop(str, i, len, eval)
        if enegate
            eval *= Int32(-1)
        end
    end

    exp = eval - frac_digits

    maxexp = 308
    minexp = -307

    if frac_digits <= 15 && -22 <= exp <= 22
        if exp >= 0
            f = F(f1)*pre_comp_exp[exp+1]
        else
            f = F(f1)/pre_comp_exp[-exp+1]
        end
    else
          f = convert_to_double(f1, exp)
    end

    if negate
        f = -f
    end

    @label done
    return R(convert(F, f)), i

    @label error
    return R(), i
end

function tryparsenext(f::Field{T}, str::Union{VectorBackedUTF8String, String}, i, len, opts::LocalOpts{T_ENDCHAR}) where {T, T_ENDCHAR<:UInt8}
    R = Nullable{T}
    i > len && @goto error
    if f.ignore_init_whitespace
        i = eatwhitespaces(str, i, len)
    end
    @chk2 res, i = tryparsenext(f.inner, str, i, len, opts)

    if f.ignore_end_whitespace
        i0 = i

        while i<=len
            @inbounds b = codeunit(str, i)

            !opts.spacedelim && opts.endchar == 0x09 && b == 0x09 && (i = i+1; @goto done) # 0x09 is \t

            b!=0x20 && b!=0x09 && break
            i=i+1
        end

        opts.spacedelim && i > i0 && @goto done
    end
    # todo don't ignore whitespace AND spacedelim

    if i > len
        if f.eoldelim
            @goto done
        else
            @goto error
        end
    end

    i>len && error("Internal error.")
    @inbounds b = codeunit(str, i)
    opts.spacedelim && (b!=0x20 || b!=0x09) && (i+=1; @goto done)
    !opts.spacedelim && opts.endchar == b && (i+=1; @goto done)

    if f.eoldelim
        if b == 0x0d # '\r'
            i+=1
            if i<=len
                @inbounds b = codeunit(str, i)
                if b == 0x0a # '\n'
                    i+=1
                end
            end
            @goto done
        elseif b == 0x0a # '\n'
            i+=1
            if i<=len
                @inbounds b = codeunit(str, i)
                if b == 0x0d # '\r'
                    i+=1
                end
            end
            @goto done
        end
    end

    @label error
    return R(), i

    @label done
    return R(convert(T, res)), i
end

function tryparsenext(q::Quoted{T,S,<:UInt8,<:UInt8}, str::Union{VectorBackedUTF8String, String}, i, len, opts::LocalOpts{<:UInt8,<:UInt8,<:UInt8}) where {T,S}
    if i>len
        q.required && @goto error
        # check to see if inner thing is ok with an empty field
        @chk2 x, i = tryparsenext(q.inner, str, i, len, opts) error
        @goto done
    end
    @inbounds b = codeunit(str, i)
    ii = i+1
    quotestarted = false
    if q.quotechar == b
        quotestarted = true
        if !q.includequotes
            i = ii
        end

        if q.stripwhitespaces
            i = eatwhitespaces(str, i, len)
        end
    else
        q.required && @goto error
    end

    if quotestarted
        qopts = LocalOpts(q.quotechar, false, q.quotechar, q.escapechar,
                         q.includequotes, q.includenewlines)
        @chk2 x, i = tryparsenext(q.inner, str, i, len, qopts)
    else
        @chk2 x, i = tryparsenext(q.inner, str, i, len, opts)
    end

    if i > len
        if quotestarted && !q.includequotes
            @goto error
        end
        @goto done
    end

    if q.stripwhitespaces
        i = eatwhitespaces(str, i, len)
    end
    i>len && error("Internal error.")
    @inbounds b = codeunit(str, i)
    ii = i + 1

    if quotestarted && !q.includequotes
        b != q.quotechar && @goto error
        i = ii
    end


    @label done
    return Nullable{T}(x), i

    @label error
    return Nullable{T}(), i
end

const INVALID_INDEX = 1000
const pre_comp_1 = UInt16[fill(INVALID_INDEX, 47); [0,1,2,3,4,5,6,7,8,9]]
const pre_comp_10 = UInt16[fill(INVALID_INDEX, 47); [0,10,20,30,40,50,60,70,80,90]]
const pre_comp_100 = UInt16[fill(INVALID_INDEX, 47); [0,100,200,300,400,500,600,700,800,900]]
const pre_comp_1000 = UInt16[fill(INVALID_INDEX, 47); [0,1000,2000,3000,4000,5000,6000,7000,8000,9000]]


const tuple_pre_comp_1 = tuple(UInt16[fill(INVALID_INDEX, 47); [0,1,2,3,4,5,6,7,8,9]]...)
const tuple_pre_comp_10 = tuple(UInt16[fill(INVALID_INDEX, 47); [0,10,20,30,40,50,60,70,80,90]]...)
const tuple_pre_comp_100 = tuple(UInt16[fill(INVALID_INDEX, 47); [0,100,200,300,400,500,600,700,800,900]]...)
const tuple_pre_comp_1000 = tuple(UInt16[fill(INVALID_INDEX, 47); [0,1000,2000,3000,4000,5000,6000,7000,8000,9000]]...)

function foo(str, i0, len)
    result = 0
    
    last_i = i0
    

    while last_i<len
        @inbounds b = codeunit(str,last_i)
        diff = b-0x30
        diff >= UInt8(10) && break
        last_i += 1
    end

    last_i -= 1

    p_end = pointer(str, last_i)

    i = i0

    @inbounds while last_i-i + 1 > 3
        result *= 10_000    

        d1 = pre_comp_1000[codeunit(str, i)]
        d2 = pre_comp_100[codeunit(str, i+1)]
        d3 = pre_comp_10[codeunit(str, i+2)]
        d4 = pre_comp_1[codeunit(str, i+3)]

        # v = Vec{4,Int64}((pre_comp_1000[codeunit(str, i)], pre_comp_100[codeunit(str, i+1)], pre_comp_10[codeunit(str, i+2)], pre_comp_1[codeunit(str, i+3)]))

        total = d1 + d2 + d3 + d4
        # total = sum(v)

        result += total
        
        i+=4
    end

    leftover_digits = last_i - i + 1

    @inbounds if leftover_digits == 1
        d1 = pre_comp_1[codeunit(str, i)]

        result = result * 10 + d1
    elseif leftover_digits == 2
        d1 = pre_comp_10[codeunit(str, i)]
        d2 = pre_comp_1[codeunit(str, i+1)]

        result = result * 100 + d1 + d2
    elseif leftover_digits == 3
        d1 = pre_comp_100[codeunit(str, i)]
        d2 = pre_comp_10[codeunit(str, i+1)]
        d3 = pre_comp_1[codeunit(str, i+2)]

        result = result * 1000 + d1 + d2 + d3
    end

    return result
end


function foo2(str, i0, len)
    result = 0

    end_index = pointer(str, len)
    
    p_end = pointer(str)
    

    while p_end<end_index
        b = unsafe_load(p_end)
        diff = b-0x30
        diff >= UInt8(10) && break
        p_end += 1
    end

    p_end -= 1

    p = pointer(str)

    @inbounds while p_end - p  >= 4
        result *= 10_000    

        d1 = tuple_pre_comp_1000[unsafe_load(p)]
        d2 = tuple_pre_comp_100[unsafe_load(p, 1)]
        d3 = tuple_pre_comp_10[unsafe_load(p, 2)]
        d4 = tuple_pre_comp_1[unsafe_load(p, 3)]

        # v = Vec{4,Int64}((pre_comp_1000[codeunit(str, i)], pre_comp_100[codeunit(str, i+1)], pre_comp_10[codeunit(str, i+2)], pre_comp_1[codeunit(str, i+3)]))
        # v = Vec{4,Int64}((tuple_pre_comp_1000[unsafe_load(p)], tuple_pre_comp_100[unsafe_load(p, 1)],tuple_pre_comp_10[unsafe_load(p, 2)], tuple_pre_comp_1[unsafe_load(p, 3)]))

        total = d1 + d2 + d3 + d4
        # total = sum(v)

        result += total
        
        p+=4
    end

    # leftover_digits = last_i - i + 1
    leftover_digits = p_end - p

    @inbounds if leftover_digits == 1
        # d1 = tuple_pre_comp_1[codeunit(str, i)]
        d1 = tuple_pre_comp_1[unsafe_load(p)]

        result = result * 10 + d1
    elseif leftover_digits == 2
        # d1 = tuple_pre_comp_10[codeunit(str, i)]
        # d2 = tuple_pre_comp_1[codeunit(str, i+1)]
        d1 = tuple_pre_comp_10[unsafe_load(p)]
        d2 = tuple_pre_comp_1[unsafe_load(p, 1)]

        result = result * 100 + d1 + d2
    elseif leftover_digits == 3
        d1 = tuple_pre_comp_100[unsafe_load(p)]
        d2 = tuple_pre_comp_10[unsafe_load(p, 1)]
        d3 = tuple_pre_comp_1[unsafe_load(p, 2)]
        # d1 = tuple_pre_comp_100[codeunit(str, i)]
        # d2 = tuple_pre_comp_10[codeunit(str, i+1)]
        # d3 = tuple_pre_comp_1[codeunit(str, i+2)]

        result = result * 1000 + d1 + d2 + d3
    end

    return result
end
