using Oscar

###############################################################################
#
#   Linking diagram over a number field
#
###############################################################################

struct NumberFieldLinkingDiagram{
    TNumField,
    TIdeal,
    TEntry
    }
    # base field and prime
    K::TNumField
    p::Int

    # distinguished prime sets
    S::Vector{TIdeal}
    SS::Vector{TIdeal}
    T::Vector{TIdeal}

    # row/column indexing
    row_primes::Vector{TIdeal}
    col_primes::Vector{TIdeal}

    # support data
    support::Dict{TIdeal, Vector{TIdeal}}

    # linking matrix
    #
    # entries:
    #   missing  -> diagonal
    #   NaN      -> prime not totally split
    #   integer  -> linking number
    #
    linking_matrix::Matrix{TEntry}
end

function generalized_class_group(S::Vector{AbsSimpleNumFieldOrderIdeal},T::Vector{AbsSimpleNumFieldOrderIdeal};n_quo=0)
    if !isempty(intersect(S, T)) || (is_empty(S) && is_empty(T))
        error("S and T must be disjoint and at least one of them must be non-empty")
    end
    if !is_empty(S) 
        O = maximal_order(base_ring(S[1]))
    else 
        O = maximal_order(base_ring(T[1]))
    end
    @assert all(maximal_order(base_ring(q)==O) for q in union(S,T))
    m = prod(S; init = one(O))
    Cl, Cl_map = ray_class_group(m; n_quo = n_quo)
    cl_S^T , _ = quo(Cl, sub(Cl, [Cl_map \ t for t in T])[1])
    return cl_S^T
end

function create_linking_diagram_of_K(
    K::AbsSimpleNumField,
    p::Int,
    S::Vector{AbsSimpleNumFieldOrderIdeal},
    SS::Vector{AbsSimpleNumFieldOrderIdeal},
    T::Vector{AbsSimpleNumFieldOrderIdeal}
)

    @assert is_prime(ZZ(p))

    @assert all(is_prime, S)
    @assert all(is_prime, SS)
    @assert all(is_prime, T)

    if !isempty(intersect(S, SS)) ||
       !isempty(intersect(S, T))  ||
       !isempty(intersect(SS, T))

        error("S, SS and T must be pairwise disjoint")
    end

    O = maximal_order(K)

    mm = prod(SS; init = one(O))

    cyclic_extensions = Dict{
        AbsSimpleNumFieldOrderIdeal,
        ClassField
    }()

    frob_maps = Dict{
        AbsSimpleNumFieldOrderIdeal,
        Any
    }()

    aut_groups = Dict{
        AbsSimpleNumFieldOrderIdeal,
        Any
    }()

    ###########################################################################
    # cyclic extensions
    ###########################################################################

    for q in S

        ClS, ClS_map = ray_class_group(mm*q; n_quo = p)

        T_subgroup = sub(ClS, [ClS_map \ t for t in T])[1]

        _, quo_map = quo(ClS, T_subgroup)

        Kq = ray_class_field(ClS_map, quo_map)

        cyclic_extensions[q] = Kq
        frob_maps[q] = frobenius_map(Kq)
        aut_groups[q] = automorphism_group(Kq)
    end

    ###########################################################################
    # support
    ###########################################################################

    support = Dict{
        AbsSimpleNumFieldOrderIdeal,
        Vector{AbsSimpleNumFieldOrderIdeal}
    }()

    for qq in SS

        support[qq] = [
            q for q in S
            if order(inertia_subgroup(cyclic_extensions[q], qq)) > 1
        ]
    end

    ###########################################################################
    # linking matrix
    ###########################################################################

    row_primes = collect(union(SS, S))
    col_primes = copy(S)

    nrows = length(row_primes)
    ncols = length(col_primes)

    linking_matrix = Matrix{Any}(undef, nrows, ncols)

    for i in 1:nrows

        q = row_primes[i]

        for j in 1:ncols

            q2 = col_primes[j]

            if q == q2
                linking_matrix[i, j] = missing
                continue
            end

            Kq2 = cyclic_extensions[q2]

            if prime_decomposition_type(Kq2, q)[1] != 1

                linking_matrix[i, j] = missing

            else

                σ = frob_maps[q2](q)

                linking_matrix[i, j] =
                    aut_groups[q2][2] \ σ
            end
        end
    end

    return NumberFieldLinkingDiagram(
        K,
        p,
        S,
        SS,
        T,
        row_primes,
        col_primes,
        support,
        linking_matrix
    )
end

###############################################################################
#
#   pretty printing
#
###############################################################################

function short_label(x)
    s = string(x)
    return replace(s, r"^Abelian group element \[(.*)\]$" => s"\1")
end

function Base.show(io::IO, ld::NumberFieldLinkingDiagram)

    nrows = length(ld.row_primes)
    ncols = length(ld.col_primes)

    SS_labels = ["P$(i)" for i in 1:length(ld.SS)]
    S_labels = ["Q$(j)" for j in 1:length(ld.S)]
    row_labels = collect(union([SS_labels[i] for i in 1:length(ld.SS)] ,[S_labels[j] for j in 1:length(ld.S)]))
    col_labels = S_labels
    M = ld.linking_matrix

    sentries = Matrix{String}(undef, nrows, ncols)

    for i in 1:nrows
        for j in 1:ncols

            x = M[i, j]

            if ismissing(x)
                sentries[i, j] = "·"
            elseif x==NaN
                sentries[i, j] = "ramified"
            else
                sentries[i, j] = short_label(x)
            end
        end
    end

    ###########################################################################
    # column widths
    ###########################################################################

    label_width = maximum(length.(row_labels))

    col_widths = [
        maximum(length.(vcat(col_labels[j], sentries[:, j]))) for j in 1:ncols
    ]

    pad(s, w) = lpad(s, w)

    ###########################################################################
    # header
    ###########################################################################

    println(io)
    println(io, "Number Field Linking Diagram for p = $(ld.p) and K = $(ld.K)")
    println(io)

    ###########################################################################
    # matrix header
    ###########################################################################

    print(io, rpad("", label_width))

    for j in 1:ncols
        print(io, "  ", pad(col_labels[j], col_widths[j]))
    end

    println(io)

    println(io,
        "-"^(label_width + 2 + sum(col_widths) + 2*ncols)
    )

    ###########################################################################
    # matrix rows
    ###########################################################################

    for i in 1:nrows

        print(io, rpad(row_labels[i], label_width))

        for j in 1:ncols
            print(io, "  ", pad(sentries[i, j], col_widths[j]))
        end

        println(io)
    end

    ###########################################################################
    # legends
    ###########################################################################

    println(io)
    println(io, "Koch set primes:")

    for i in 1:length(ld.SS)
        println(io, "  ", SS_labels[i], " = ", ld.SS[i])
    end

    println(io)
    println(io, "Primes in S:")

    for j in 1:length(ld.S)
        println(io, "  ", S_labels[j], " = ", ld.S[j])
    end

    ###########################################################################
    # support
    ###########################################################################

    println(io)
    println(io, "Support sets:")

    for q in ld.SS

        supp = ld.support[q]

        println(io)
        print(io, " Support set of ", q)

        if isempty(supp)
            println(io, "    ∅")
        else
            for x in supp
                print(io, "    { ", x)
            end
            println(io, " }")
        end
    end
end