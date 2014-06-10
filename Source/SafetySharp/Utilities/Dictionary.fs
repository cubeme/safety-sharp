namespace SafetySharp.Utilities
open System.Collections.Immutable

/// Type abbreviation for the <see cref="System.Collections.Immutable.ImmutableDictionary{K, V}" /> type.
type Dictionary<'K, 'V> = ImmutableDictionary<'K, 'V>

[<RequireQualifiedAccess>]
module Dictionary =
    let ofSeq (key : 'a -> 'b) (value : 'a -> 'c) (s : seq<'a>)  = s.ToImmutableDictionary(key, value)