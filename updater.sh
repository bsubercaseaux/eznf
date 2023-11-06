#!/bin/bash

# Exit in case of error
set -e

# Configuration
PACKAGE_NAME="eznf"
VERSION_FILE="setup.py"
PYPROJECT_TOML="pyproject.toml"

# Extract current version from setup.py
CURRENT_VERSION=$(awk '/version=/' $VERSION_FILE | sed "s/.*version='\([^']*\)'.*/\1/")
IFS='.' read -ra VERSION <<< "$CURRENT_VERSION"
MAJOR=${VERSION[0]}
MINOR=${VERSION[1]}
PATCH=${VERSION[2]}

NEW_MINOR=$((MINOR + 1))
NEW_VERSION="$MAJOR.$NEW_MINOR.$PATCH"

echo "Current version: $CURRENT_VERSION"
echo "New version: $NEW_VERSION"

# Create a new virtual environment
python3 -m venv venv
source venv/bin/activate

# Update the version number in setup.py
sed -i.bak "s/version='$CURRENT_VERSION'/version='$NEW_VERSION'/" $VERSION_FILE
echo "Updated $VERSION_FILE to version $NEW_VERSION"

# Update the version number in pyproject.toml
if [ -f "$PYPROJECT_TOML" ]; then
    echo "Found $PYPROJECT_TOML. Updating version..."
    sed -i.bak "s/^version = \"[^\"]*\"/version = \"$NEW_VERSION\"/" $PYPROJECT_TOML
    if grep -q "version = \"$NEW_VERSION\"" $PYPROJECT_TOML; then
        echo "Successfully updated $PYPROJECT_TOML to version $NEW_VERSION"
    else
        echo "Failed to update $PYPROJECT_TOML"
        exit 1
    fi
    rm "$PYPROJECT_TOML.bak"
else
    echo "$PYPROJECT_TOML not found, skipping update."
fi

# Install build tools
pip install --upgrade pip setuptools wheel twine build

# Clear out the old dist files
echo "Cleaning old builds from dist/"
rm -rf dist/*


# Build the package with pyproject.toml standards
python -m build

# Upload the package to PyPI
echo "Uploading new build to PyPI"
twine upload dist/*

# Cleanup and deactivate the virtual environment
rm -rf venv
rm $VERSION_FILE.bak

echo "Upload complete."
