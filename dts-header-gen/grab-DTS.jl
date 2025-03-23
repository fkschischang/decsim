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
function grabDTS(L,M)
    if M == 1
        DTS = trivial_dts(L);
    elseif M == 2;
        DTS = skokeefe(L);
    elseif M == 3 || M == 4
        DTS_name_list = readdir("scope-optimal-DTSs/");
        DTS_index = findlast(startswith.(DTS_name_list, string(L)*"-"*string(M)));
        if DTS_index == nothing
            throw("L and M combination is currently unsupported!")
        else
            DTS = readdlm("scope-optimal-DTSs/"*DTS_name_list[DTS_index], Int64);
        end 
    elseif L == 1 && M == 5
        DTS = [0 1 4 10 12 17]
    elseif L == 1 && M == 6
        DTS = [0 1 4 10 18 23 25]
    elseif L == 1 && M == 7
        DTS = [0 1 4 9 15 22 32 34]
    elseif L == 1 && M == 8
        DTS = [0 1 5 12 25 27 35 41 44]
    elseif L == 1 && M == 9
        DTS = [0 1 6 10 23 26 34 41 53 55]
    else
        throw("L and M combination is currently unsupported!")
    end
end;
