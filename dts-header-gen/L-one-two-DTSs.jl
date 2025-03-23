#=
MIT License

Copyright (c) 2024 Mohannad Shehadeh

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
=#
function getSpectrum(X)
   SPECTRUM = []
       for block in 1:size(X)[1]
           for i in 1:size(X)[2]
               for j in i+1:size(X)[2]
                   push!(SPECTRUM, abs(X[block,i]-X[block,j]))
               end
           end
       end
   return SPECTRUM
end
mlen(X) = maximum(getSpectrum(X));
slen(X) = sum([maximum(getSpectrum(X[i,:]')) for i in 1:size(X)[1]]);
verify(X) = (size(X)[1],size(X)[2]-1,mlen(X),slen(X),allunique(getSpectrum(X)));
sort_dts(X) = X[sortperm([maximum(getSpectrum(X[i,:]')) for i in 1:size(X)[1]],rev=true),:];
trivial_dts(n) = [j == 1 ? 0 : n-(i-1) for i in 1:n, j in 1:2];
function skolem_0(n)
    @assert n%4 == 0
    local m = floor(Int64,n/4)
    @assert m > 1
    local X = zeros(Int64,n,3)
    X[1,:] = [0,4*m-1,10*m]
    X[2,:] = [0,2*m-1,8*m-1]
    X[3,:] = [0,1,5*m+1]
    for i in 0:2*m-1
        X[4+i,:] = [0,4*m-2*i,12*m-i]
    end
    for i in 1:m-1
        X[4+2*m-1+i,:] = [0,4*m-1-2*i,8*m-1-i]
    end
    for i in 0:m-3
        X[4+3*m-1+i,:] = [0,2*m-3-2*i,7*m-1-i]
    end
    return X
end;
function skolem_1(n)
    @assert n%4 == 1
    local m = floor(Int64,n/4)
    @assert m > 1
    local X = zeros(Int64,n,3)
    X[1,:] = [0,4*m+1,10*m+3]
    X[2,:] = [0,2*m-1,8*m+2]
    X[3,:] = [0,1,5*m+3]
    for i in 0:2*m-1
        X[4+i,:] = [0,4*m-2*i,12*m+3-i]
    end
    for i in 1:m
        X[4+2*m-1+i,:] = [0,4*m+1-2*i,8*m+2-i]
    end
    for i in 1:m-2
        X[4+3*m-1+i,:] = [0,2*m-1-2*i,7*m+2-i]
    end
    return X
end;
function okeefe_2(n)
    @assert n%4 == 2
    local m = floor(Int64,n/4)
    @assert m > 1
    local X = zeros(Int64,n,3)
    X[1,:] = [0,4*m+1,10*m+4]
    X[2,:] = [0,2*m+1,10*m+5]
    X[3,:] = [0,4*m+2,12*m+7]
    X[4,:] = [0,1,11*m+6]
    for i in 1:2*m
        X[4+i,:] = [0,4*m+2-2*i,8*m+4-i]
    end
    for i in 1:m-1
        X[4+2*m+i,:] = [0,4*m+1-2*i,12*m+6-i]
    end
    for i in 1:m-1
        X[4+3*m-1+i,:] = [0,2*m+1-2*i,11*m+5-i]
    end
    return X
end;
function okeefe_3(n)
    @assert n%4 == 3
    local m = floor(Int64,n/4)
    @assert m > 1
    local X = zeros(Int64,n,3)
    X[1,:] = [0,2*m+3,7*m+6]
    X[2,:] = [0,1,5*m+5]
    X[3,:] = [0,2*m+1,8*m+6]
    X[4,:] = [0,4*m+2,10*m+8]
    X[5,:] = [0,4*m+3,12*m+10]
    for i in 1:2*m
        X[5+i,:] = [0,4*m+2-2*i,12*m+9-i]
    end
    for i in 1:m-1
        X[5+2*m+i,:] = [0,4*m+3-2*i,8*m+6-i]
    end
    for i in 1:m-1
        X[5+3*m-1+i,:] = [0,2*m+1-2*i,7*m+6-i]
    end
    return X
end;
function skokeefe(n)
    if n == 1
        X = 
        [
        0 1 3 
        ];
        return sort_dts(X)
    elseif n == 2
        X = 
        [
        0 3 4 
        0 2 7
        ];
        return sort_dts(X)
    elseif n == 3
        X = 
        [
        0 4 5 
        0 3 10 
        0 6 8
        ];
        return sort_dts(X)
    elseif n == 4
        X = 
        [
        0 3 8 
        0 2 9 
        0 4 10 
        0 11 12
        ];
        return sort_dts(X)
    elseif n == 5
        X = 
        [
        0 6 14 
        0 13 15 
        0 3 10 
        0 11 12 
        0 5 9 
        ];
        return sort_dts(X)
    elseif n == 6
        X = 
        [
        0 7 11 
        0 12 17 
        0 2 10 
        0 3 19 
        0 1 14 
        0 6 15   
        ];
        return sort_dts(X)
    elseif n == 7
        X = 
        [
        0 9 16 
        0 12 15 
        0 5 13 
        0 6 17 
        0 4 14 
        0 2 22 
        0 1 19
        ];
        return sort_dts(X)
    elseif n%4 == 0
        return sort_dts(skolem_0(n))
    elseif n%4 == 1 
        return sort_dts(skolem_1(n))
    elseif n%4 == 2
        return sort_dts(okeefe_2(n))
    elseif n%4 == 3
        return sort_dts(okeefe_3(n))
    end
end;