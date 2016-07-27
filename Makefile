docs: 
	pandoc -f markdown+lhs -t markdown src/MicroKanren.lhs | sed -e 's/{.sourceCode .literate .haskell}/haskell/' > doc/MicroKanren.md
