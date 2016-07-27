DOCS=MicroKanren

docs: $(DOCS)

$(DOCS):
	pandoc -f markdown+lhs -t markdown src/$@.lhs | sed -e 's/{.sourceCode .literate .haskell}/haskell/' > doc/$@.md
