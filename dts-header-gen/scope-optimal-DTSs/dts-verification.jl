using DelimitedFiles;
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
end;
mlen(X) = maximum(getSpectrum(X));
slen(X) = sum([maximum(getSpectrum(X[i,:]')) for i in 1:size(X)[1]]);
verify(X) = (size(X)[1],size(X)[2]-1,mlen(X),slen(X),allunique(getSpectrum(X)));
sort_dts(X) = X[sortperm([maximum(getSpectrum(X[i,:]')) for i in 1:size(X)[1]],rev=true),:];
function write_dts(X)
	local Y = sort_dts(X)
    @assert verify(Y)[5] == true
    local name = string(verify(Y)[1])*"-"*string(verify(Y)[2])*"-"*string(verify(Y)[3])*"-"*string(verify(Y)[4])*".txt"
	writedlm(name,Y)
end;
