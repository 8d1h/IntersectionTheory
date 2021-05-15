using Documenter, IntersectionTheory
makedocs(modules = [IntersectionTheory], sitename = "IntersectionTheory.jl",
	 pages = ["About" => "index.md",
		  "Documentation" => ["intro.md", "constructors.md", "varieties.md", "bundles.md", "morphisms.md"],
		  "Examples" => ["cubic_fourfold.md", "curves_on_quintic.md"],
		  "dev.md"])
deploydocs(repo = "github.com/8d1h/IntersectionTheory.git")
