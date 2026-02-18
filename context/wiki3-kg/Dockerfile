# Use the official Weaviate image as a base
FROM cr.weaviate.io/semitechnologies/weaviate:latest

# Tell the container to listen on both main API ports
EXPOSE 8080 50051

# Default environment for Weaviate
ENV AUTHENTICATION_ANONYMOUS_ACCESS_ENABLED=true
ENV QUERY_DEFAULTS_LIMIT=25
ENV PERSISTENCE_DATA_PATH=/var/lib/weaviate

# Enable Ollama modules for embeddings + generative RAG
ENV ENABLE_MODULES=text2vec-ollama,generative-ollama

# Default Ollama API endpoint to your host machine
# host.docker.internal resolves to the macOS host from inside Docker
ENV OLLAMA_API_ENDPOINT=http://host.docker.internal:11434
