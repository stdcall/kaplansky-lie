#import "main-defs.typ": *
#import "statements.typ": bib-entry, bib-group
#import "bibliography-style.typ": bib-description
#import "bibliography-data.typ": editorial-bibliography as editorial-records

#unnumbered-chapter[Список литературы]
#metadata(none) <bibliography-start>

#bib-entry[#bib-description("Block1960")] <bib:Block1960>
#bib-entry[#bib-description("Block1962")] <bib:Block1962>
#bib-entry[#bib-description("Block1965")] <bib:Block1965>
#bib-entry[#bib-description("Block1964")] <bib:Block1964>
#bib-entry[#bib-description("Bourbaki1960")] <bib:Bourbaki1960>
#bib-entry[#bib-description("Winter1968")] <bib:Winter1968>
#bib-entry[#bib-description("Gelfand1941")] <bib:Gelfand1941>
#bib-entry[#bib-description("Gleason1952")] <bib:Gleason1952>
#bib-entry[#bib-description("Glushkov1957")] <bib:Glushkov1957>
#bib-entry[#bib-description("Jacobson1962")] <bib:Jacobson1962>
#bib-entry[#bib-description("Seligman1956")] <bib:Seligman1956>
#bib-entry[#bib-description("Seligman1957a")] <bib:Seligman1957a>
#bib-entry[#bib-description("Seligman1967")] <bib:Seligman1967>
#bib-entry[#bib-description("Seligman1957b")] <bib:Seligman1957b>
#bib-entry[#bib-description("Kaplansky1958")] <bib:Kaplansky1958>
#bib-entry[#bib-description("Kreknin1963")] <bib:Kreknin1963>
#bib-entry[#bib-description("Loomis1953")] <bib:Loomis1953>
#bib-entry[#bib-description("Mills1957")] <bib:Mills1957>
#bib-entry[#bib-description("Montgomery1952")] <bib:Montgomery1952>
#bib-entry[#bib-description("Montgomery1955")] <bib:Montgomery1955>
#bib-entry[#bib-description("Serre1966")] <bib:Serre1966>
#bib-entry[#bib-description("Chevalley1951")] <bib:Chevalley1951>
#bib-entry[#bib-description("Shoenfield1956")] <bib:Shoenfield1956>
#bib-entry[#bib-description("Schue1960")] <bib:Schue1960>
#bib-entry[#bib-description("Zassenhaus1959")] <bib:Zassenhaus1959>
#bib-entry[#bib-description("Jacoby1957")] <bib:Jacoby1957>
#bib-entry[#bib-description("Yamabe1953a")] <bib:Yamabe1953a>
#bib-entry[#bib-description("Yamabe1953b")] <bib:Yamabe1953b>
#bib-entry[#bib-description("SeminaireLie1955")] <bib:SeminaireLie1955>

// The literature of the editorial notes (editorial.bib), printed after
// the list of the book once it has records.
#if editorial-records.len() > 0 [
  #bib-group[Литература редакционных примечаний]
]

#metadata(none) <bibliography-end>
