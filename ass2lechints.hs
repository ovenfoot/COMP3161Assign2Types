--Hints from Gabi

data Type = Arrow Type Type
			| Prod Type Type
			| Sum Type Type
			| Base Basteype
			


--etc

freshname:: TC Id

typeError -whenever you can't unify the type properly

substGamma subtitute into the envrionment

Get unificaiton done as quckly as possible

