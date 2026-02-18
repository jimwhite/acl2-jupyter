

```bash
docker volume create weaviate_data
```

```bash
docker build -t weaviate-local-ollama .
```

```bash
docker run -d \
  --name weaviate_local \
  -p 8080:8080 \
  -p 50051:50051 \
  --mount type=volume,src=weaviate_data,dst=/var/lib/weaviate \
  weaviate-local-ollama
```
